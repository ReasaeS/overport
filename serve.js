#!/usr/bin/env node
'use strict';

const net = require('net');
const fs = require('fs');
const path = require('path');
const os = require('os');
const crypto = require('crypto');
const { spawn, execSync } = require('child_process');

// ======================
// Configuration
// ======================
let PORT = 9001;
let HOST = '127.0.0.1';
const START_PORT = PORT;
const MAX_PORT = 65535;

const SCRIPT_DIR = path.dirname(fs.realpathSync(process.argv[1]));

const WEB_ROOT = process.argv[2] || path.join(process.cwd(), 'src');

let REAL_WEB_ROOT;
try {
    REAL_WEB_ROOT = fs.realpathSync(WEB_ROOT);
    if (!fs.statSync(REAL_WEB_ROOT).isDirectory()) throw new Error('not a directory');
} catch (e) {
    process.stderr.write(`Invalid web root: ${WEB_ROOT}\n`);
    process.exit(1);
}

const ROOT_PREFIX = REAL_WEB_ROOT.endsWith('/') ? REAL_WEB_ROOT : REAL_WEB_ROOT + '/';

const INDEX_FILE = path.join(REAL_WEB_ROOT, 'index.html');
const PAGE_404 = path.join(SCRIPT_DIR, 'status', 'status.html');
let REAL_PAGE_404;
try { REAL_PAGE_404 = fs.realpathSync(PAGE_404); } catch (e) { REAL_PAGE_404 = undefined; }

const STATE_HOME = (process.env.XDG_STATE_HOME && process.env.XDG_STATE_HOME.length)
    ? process.env.XDG_STATE_HOME
    : path.join(process.env.HOME || os.homedir(), '.local', 'state');
const HISTORY_DIR = path.join(STATE_HOME, 'overport');
const SETTINGS_FILE = path.join(HISTORY_DIR, 'settings.pref');
const BUFFER_SIZE = 8192;
const MAX_REQUEST_SIZE = 16384;
const READ_TIMEOUT = 5;
const SEND_STALL_TIMEOUT = 30;

let HOT_RELOAD = true;
const HOT_RELOAD_PATH = '/__hotreload';
const HOT_RELOAD_POLL_MS = 1000;
let HOT_RELOAD_MODE = 'poll'; // 'poll' (client polls) or 'push' (server pushes over a WebSocket)

// ---- WebSocket push mode state ----
const WS_GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11'; // RFC 6455 handshake magic
const WS_SCAN_INTERVAL_MS = 1000; // ms between web-root scans while clients are connected

let wsClients = [];              // live WebSocket connections: { socket, ip, buf }
let lastWsSignature;             // web-root signature the monitor last observed
let lastWsScanAt = 0;
let wsReloadCount = 0;
let lastWsReload;                // human-readable timestamp of the last pushed reload
let lastWsReloadEpoch;

const MIME_TYPES = {
    html: 'text/html', htm: 'text/html', txt: 'text/plain', css: 'text/css',
    js: 'application/javascript', json: 'application/json', png: 'image/png',
    jpg: 'image/jpeg', jpeg: 'image/jpeg', gif: 'image/gif', svg: 'image/svg+xml',
    ico: 'image/x-icon', pdf: 'application/pdf', zip: 'application/zip',
    gz: 'application/gzip', mp3: 'audio/mpeg', mp4: 'video/mp4', webm: 'video/webm',
    woff: 'font/woff', woff2: 'font/woff2', ttf: 'font/ttf', otf: 'font/otf',
};

// ======================
// TUI color scheme
//   FRAME - structural chrome: borders, separators, rules
//   LABEL - section titles and field names
//   VALUE - data: paths, IPs, sizes, timestamps, URLs
//   GOOD  - healthy/live state, 2xx-3xx responses, follow mode
//   WARN  - degraded state, 4xx responses, scrolled mode, warnings
//   BAD   - errors/dead state, 5xx responses
//   MUTED - secondary text: hints, ages, counters
// ======================
const RESET = '\x1b[0m';
const FRAME = '\x1b[95m';
const LABEL = '\x1b[1;96m';
const VALUE = '\x1b[97m';
const GOOD = '\x1b[92m';
const WARN = '\x1b[93m';
const BAD = '\x1b[91m';
const MUTED = '\x1b[90m';

const IS_TTY = Boolean(process.stdout.isTTY);
let TERM_ROWS, TERM_COLS;
const BAR_HEIGHT = 7;
const LOG_WIDTH = 80;

let lastHotReload;
let lastPollEpoch;
let pollCount = 0;
let requestCount = 0;
let totalBytesSent = 0;
let xferWindow = [];
let XFER_WINDOW_SECS = 60;

let powerWatts;
let powerSource;
let lastPowerSampleAt = 0;
let POWER_SAMPLE_INTERVAL = 5;
let powerEverOk = false;
const POWER_ROOT_HINT_AFTER = 20;
const SERVER_START_TIME = Math.floor(Date.now() / 1000);
let powerMonitorEnabled = true;

let lastRaplUj;
let lastRaplTime;

let streamCounter = 0;
let lastTime = Math.floor(Date.now() / 1000) - 5;
let starSeed = Math.floor(Math.random() * 0x7FFFFFFF);
let historyReady = false;

let logLines = [];
let scrollOffset = 0;
const MAX_LOG_LINES = 2000;
let tuiActive = false;

let targetFps = 15;
let lastRedrawAt = 0;
let redrawPending = false;

let confirmOpen = false;
let confirmChoice = 0;

let noticeOpen = false;
let noticeText = [];

let muted = false;
let toneVolume = 1.0;

let starsEnabled = true;
let starDensityScale = 1.0;
let starColorsEnabled = true;

let kwhCost;

let stressTestRate = 10;
let stressTestDuration = 10;
let stressTestRunning = false;

let logCleanupEnabled = false;
let logMaxAge = 3600;

let networkAccess = 'local'; // 'local' (127.0.0.1) or 'lan' (0.0.0.0, all interfaces)
let lanIp;                   // cached best-guess LAN-reachable address while networkAccess === 'lan'
let lastLanIpCheckAt = 0;
const LAN_IP_CHECK_INTERVAL_MS = 10000;

let settingsOpen = false;
let settingsIndex = 0;
let settingsEditing = false;
let settingsEditBuffer = '';
let settingsFlash = '';

const STAR_LAYERS = [
    {
        speed: 0.25, char: '.', density: 35,
        colors: ['\x1b[2;34m', '\x1b[38;5;60m', '\x1b[38;5;66m', '\x1b[38;5;95m'],
        twinkle: '\x1b[94m',
    },
    {
        speed: 0.50, char: '+', density: 24,
        colors: ['\x1b[34m', '\x1b[38;5;104m', '\x1b[38;5;130m', '\x1b[38;5;96m'],
        twinkle: '\x1b[1;94m',
    },
    {
        speed: 0.75, char: '*', density: 15,
        colors: ['\x1b[94m', '\x1b[38;5;111m', '\x1b[38;5;208m', '\x1b[38;5;135m'],
        twinkle: '\x1b[1;38;5;153m',
    },
];

[TERM_ROWS, TERM_COLS] = terminalSize();

// ======================
// Sound synthesis
// ======================

const SAMPLE_RATE = 22050;
const PI = Math.PI;

const PLAYER_CANDIDATES = [
    ['paplay'],
    ['aplay', '-q', '-'],
    ['play', '-q', '-t', 'wav', '-'],
];

const TONE_SPEC = {
    error: [
        { freq: 160, freq_end: 110, duration: 0.11, wave: 'square', volume: 0.20, gap: 0.06 },
        { freq: 160, freq_end: 110, duration: 0.11, wave: 'square', volume: 0.20 },
    ],
    warn: [
        { freq: 420, freq_end: 450, duration: 0.08, wave: 'sine', volume: 0.18, gap: 0.05 },
        { freq: 520, freq_end: 560, duration: 0.10, wave: 'sine', volume: 0.18 },
    ],
    packet: [
        { freq: 480, duration: 0.06, wave: 'sine', volume: 0.13 },
    ],
    stream: [
        { freq: 260, duration: 0.08, wave: 'sine', vibrato_hz: 8, vibrato_depth: 0.02, volume: 0.16, gap: 0.025 },
        { freq: 330, duration: 0.08, wave: 'sine', vibrato_hz: 8, vibrato_depth: 0.02, volume: 0.16, gap: 0.025 },
        { freq: 392, duration: 0.14, wave: 'sine', vibrato_hz: 8, vibrato_depth: 0.02, volume: 0.18 },
    ],
    browser: [
        { freq: 200, freq_end: 520, duration: 0.32, wave: 'sine', vibrato_hz: 10, vibrato_depth: 0.015, volume: 0.18 },
    ],
};

function detectAudioPlayer() {
    const dirs = (process.env.PATH || '').split(path.delimiter);
    for (const cand of PLAYER_CANDIDATES) {
        for (const dir of dirs) {
            if (!dir) continue;
            try {
                fs.accessSync(path.join(dir, cand[0]), fs.constants.X_OK);
                return cand;
            } catch (e) { /* not found here */ }
        }
    }
    return [];
}

function synthSegment(o) {
    const freq0 = o.freq;
    const freq1 = o.freq_end !== undefined ? o.freq_end : o.freq;
    const dur = o.duration;
    const wave = o.wave || 'sine';
    const vibHz = o.vibrato_hz || 0;
    const vibDepth = o.vibrato_depth || 0;
    const vol = (o.volume !== undefined ? o.volume : 0.5) * toneVolume;

    const n = Math.floor(SAMPLE_RATE * dur);
    if (n < 1) return [];

    const attack = Math.floor(n * 0.08) || 1;
    const release = Math.floor(n * 0.15) || 1;

    const samples = new Array(n);
    let phase = 0;
    for (let i = 0; i < n; i++) {
        const t = i / SAMPLE_RATE;
        const pos = n > 1 ? i / (n - 1) : 0;
        let freq = freq0 + (freq1 - freq0) * pos;
        if (vibHz) freq += vibDepth * freq0 * Math.sin(2 * PI * vibHz * t);

        phase += 2 * PI * freq / SAMPLE_RATE;

        let s;
        if (wave === 'square') {
            s = Math.sin(phase) >= 0 ? 1 : -1;
        } else if (wave === 'saw') {
            const cycles = phase / (2 * PI);
            s = 2 * (cycles - Math.floor(cycles + 0.5));
        } else {
            s = Math.sin(phase);
        }

        let env = 1;
        if (i < attack) env = i / attack;
        if (i >= n - release) env = (n - 1 - i) / release;
        if (env < 0) env = 0;
        if (env > 1) env = 1;

        samples[i] = s * env * vol;
    }

    return samples;
}

function synthTone(segments) {
    let samples = [];
    for (const seg of segments) {
        samples = samples.concat(synthSegment(seg));
        const gapN = Math.floor(SAMPLE_RATE * (seg.gap || 0));
        for (let i = 0; i < gapN; i++) samples.push(0);
    }
    return samples;
}

function wavBytes(samples) {
    const data = Buffer.alloc(samples.length * 2);
    for (let i = 0; i < samples.length; i++) {
        let v = Math.floor(samples[i] * 32767);
        if (v > 32767) v = 32767;
        if (v < -32768) v = -32768;
        data.writeInt16LE(v, i * 2);
    }

    const byteRate = SAMPLE_RATE * 2;
    const dataLen = data.length;
    const riffLen = 36 + dataLen;

    const header = Buffer.alloc(44);
    header.write('RIFF', 0, 'ascii');
    header.writeUInt32LE(riffLen, 4);
    header.write('WAVE', 8, 'ascii');
    header.write('fmt ', 12, 'ascii');
    header.writeUInt32LE(16, 16);
    header.writeUInt16LE(1, 20);
    header.writeUInt16LE(1, 22);
    header.writeUInt32LE(SAMPLE_RATE, 24);
    header.writeUInt32LE(byteRate, 28);
    header.writeUInt16LE(2, 32);
    header.writeUInt16LE(16, 34);
    header.write('data', 36, 'ascii');
    header.writeUInt32LE(dataLen, 40);

    return Buffer.concat([header, data]);
}

let AUDIO_CMD = detectAudioPlayer();
let TONE_WAV = {};
const LAST_TONE_AT = {};
const TONE_MIN_GAP = 0.15;

function rebuildToneWav() {
    TONE_WAV = {};
    for (const key of Object.keys(TONE_SPEC)) {
        TONE_WAV[key] = wavBytes(synthTone(TONE_SPEC[key]));
    }
}

rebuildToneWav();

function getPwuid(uid) {
    try {
        const data = fs.readFileSync('/etc/passwd', 'utf8');
        for (const line of data.split('\n')) {
            if (!line) continue;
            const parts = line.split(':');
            if (parts.length >= 7 && parseInt(parts[2], 10) === uid) {
                return { name: parts[0], home: parts[5] };
            }
        }
    } catch (e) { /* no /etc/passwd (e.g. non-Linux) */ }
    return null;
}

function childEnvAndIds() {
    if (typeof process.getuid !== 'function' || process.getuid() !== 0) return { env: process.env };
    if (!process.env.SUDO_UID || !process.env.SUDO_GID) return { env: process.env };

    const uid = parseInt(process.env.SUDO_UID, 10);
    const gid = parseInt(process.env.SUDO_GID, 10);
    const env = Object.assign({}, process.env);
    const pw = getPwuid(uid);
    if (pw) {
        env.HOME = pw.home;
        env.USER = pw.name;
        env.LOGNAME = pw.name;
    }
    env.XDG_RUNTIME_DIR = `/run/user/${uid}`;

    return { env, uid, gid };
}

function playTone(category) {
    if (muted || toneVolume === 0) return;
    if (!AUDIO_CMD.length || !TONE_WAV[category]) return;

    const now = Date.now() / 1000;
    if (LAST_TONE_AT[category] !== undefined && (now - LAST_TONE_AT[category]) < TONE_MIN_GAP) return;
    LAST_TONE_AT[category] = now;

    const { env, uid, gid } = childEnvAndIds();
    const [cmd, ...args] = AUDIO_CMD;

    try {
        const child = spawn(cmd, args, { stdio: ['pipe', 'ignore', 'ignore'], env, uid, gid, detached: true });
        child.on('error', () => {});
        child.stdin.on('error', () => {});
        child.stdin.write(TONE_WAV[category]);
        child.stdin.end();
        child.unref();
    } catch (e) { /* best-effort playback */ }
}

// ======================
// Bandwidth tracking
// ======================

function recordTransfer(bytes) {
    if (!bytes || bytes <= 0) return;
    totalBytesSent += bytes;
    xferWindow.push([Math.floor(Date.now() / 1000), bytes]);
}

function bytesPerWindow() {
    const cutoff = Math.floor(Date.now() / 1000) - XFER_WINDOW_SECS;
    while (xferWindow.length && xferWindow[0][0] < cutoff) xferWindow.shift();

    let sum = 0;
    for (const [, b] of xferWindow) sum += b;
    return sum;
}

function formatDataSize(bytes) {
    if (bytes === undefined || bytes === null || bytes < 0) bytes = 0;

    const bits = bytes * 8;
    if (bits < 8) return bits === 1 ? '1 bit' : `${bits} bits`;

    const units = ['B', 'KiB', 'MiB', 'GiB', 'TiB', 'PiB', 'EiB'];
    let value = bytes;
    let unit = units.shift();
    while (value >= 1024 && units.length) {
        value /= 1024;
        unit = units.shift();
    }

    return unit === 'B' ? `${value} ${unit}` : `${value.toFixed(2)} ${unit}`;
}

// ======================
// Power monitoring
// ======================

function readFirstLine(p) {
    try {
        const line = fs.readFileSync(p, 'utf8').split('\n')[0].trim();
        return /^-?\d+$/.test(line) ? parseInt(line, 10) : undefined;
    } catch (e) { return undefined; }
}

function discoverRaplDomains() {
    const base = '/sys/class/powercap';
    let entries;
    try { entries = fs.readdirSync(base); } catch (e) { return []; }

    const matches = entries.filter(name => {
        if (!/^\w+-rapl:\d+$/.test(name)) return false;
        try { fs.accessSync(path.join(base, name, 'energy_uj'), fs.constants.R_OK); return true; }
        catch (e) { return false; }
    });
    matches.sort();

    return matches.map(name => path.join(base, name, 'energy_uj'));
}

function readRaplEnergy(paths) {
    let total = 0;
    let any = false;
    for (const p of paths) {
        const v = readFirstLine(p);
        if (v === undefined) continue;
        total += v;
        any = true;
    }
    return any ? total : undefined;
}

function samplePowerLinuxBattery() {
    let entries;
    try { entries = fs.readdirSync('/sys/class/power_supply'); } catch (e) { return undefined; }

    for (const name of entries) {
        if (!name.startsWith('BAT')) continue;
        const bat = path.join('/sys/class/power_supply', name);

        let powerUw = readFirstLine(path.join(bat, 'power_now'));
        if (powerUw === undefined) {
            const i = readFirstLine(path.join(bat, 'current_now'));
            const v = readFirstLine(path.join(bat, 'voltage_now'));
            if (i !== undefined && v !== undefined) powerUw = (i * v) / 1_000_000;
        }

        if (powerUw !== undefined && powerUw > 0) return powerUw / 1_000_000;
    }

    return undefined;
}

function samplePowerLinux() {
    const domains = discoverRaplDomains();

    if (domains.length) {
        const nowUj = readRaplEnergy(domains);
        const nowT = Math.floor(Date.now() / 1000);

        let watts;
        if (nowUj !== undefined && lastRaplUj !== undefined && nowT > lastRaplTime) {
            const deltaUj = nowUj - lastRaplUj;
            if (deltaUj > 0) watts = (deltaUj / 1_000_000) / (nowT - lastRaplTime);
        }

        if (nowUj !== undefined) lastRaplUj = nowUj;
        lastRaplTime = nowT;

        return [watts, 'RAPL'];
    }

    const battWatts = samplePowerLinuxBattery();
    if (battWatts !== undefined) return [battWatts, 'battery'];

    return [undefined, undefined];
}

function samplePowerDarwin() {
    let out;
    try { out = execSync('ioreg -rn AppleSmartBattery -w0 2>/dev/null').toString(); }
    catch (e) { return [undefined, undefined]; }
    if (!out) return [undefined, undefined];

    const ampMatch = out.match(/"(?:InstantAmperage|Amperage)"\s*=\s*(-?\d+)/);
    const voltMatch = out.match(/"Voltage"\s*=\s*(-?\d+)/);
    if (!ampMatch || !voltMatch) return [undefined, undefined];

    let amperage = BigInt(ampMatch[1]);
    const voltage = parseInt(voltMatch[1], 10);
    if (voltage <= 0) return [undefined, undefined];

    if (amperage > 2n ** 63n) amperage -= 2n ** 64n;

    const watts = Math.abs(Number(amperage)) * voltage / 1_000_000;
    return [watts, 'battery'];
}

function samplePowerWindows() {
    const ps = 'Get-CimInstance -Namespace root/wmi -ClassName BatteryStatus -ErrorAction SilentlyContinue '
             + '| Select-Object -First 1 '
             + '| ForEach-Object { if ($_.DischargeRate -gt 0) { $_.DischargeRate } elseif ($_.ChargeRate -gt 0) { $_.ChargeRate } else { 0 } }';

    let out;
    try { out = execSync(`powershell -NoProfile -NonInteractive -Command "${ps}" 2>NUL`).toString(); }
    catch (e) { return [undefined, undefined]; }

    const m = out.match(/(\d+)/);
    if (!m) return [undefined, undefined];

    const mw = parseInt(m[1], 10);
    if (mw === 0) return [undefined, undefined];
    return [mw / 1000, 'WMI'];
}

function samplePower() {
    if (!powerMonitorEnabled) {
        powerWatts = undefined;
        powerSource = undefined;
        return;
    }

    const now = Math.floor(Date.now() / 1000);
    if (now - lastPowerSampleAt < POWER_SAMPLE_INTERVAL) return;
    lastPowerSampleAt = now;

    let watts, source;
    if (process.platform === 'linux') [watts, source] = samplePowerLinux();
    else if (process.platform === 'darwin') [watts, source] = samplePowerDarwin();
    else if (process.platform === 'win32') [watts, source] = samplePowerWindows();
    else [watts, source] = [undefined, undefined];

    if (source !== undefined) {
        powerSource = source;
        if (watts !== undefined) {
            powerWatts = watts;
            powerEverOk = true;
        }
    } else {
        powerSource = undefined;
        powerWatts = undefined;
    }
}

function formatCost(amount) {
    if (amount >= 0.01) return amount.toFixed(2);
    if (amount >= 0.0001) return amount.toFixed(4);
    return amount.toFixed(6);
}

// ======================
// Stress testing
// ======================

function collectWebRootFiles() {
    const files = [];
    function walk(dir) {
        let entries;
        try { entries = fs.readdirSync(dir, { withFileTypes: true }); } catch (e) { return; }
        for (const entry of entries) {
            const full = path.join(dir, entry.name);
            if (entry.isDirectory()) walk(full);
            else if (entry.isFile()) {
                let rel = full.slice(REAL_WEB_ROOT.length);
                if (!rel.startsWith('/')) rel = '/' + rel;
                files.push(rel);
            }
        }
    }
    walk(REAL_WEB_ROOT);
    return files;
}

function sleep(ms) { return new Promise(r => setTimeout(r, ms)); }

function httpGetOk(host, port, reqPath) {
    return new Promise(resolve => {
        let done = false;
        const finish = ok => {
            if (done) return;
            done = true;
            clearTimeout(timer);
            sock.destroy();
            resolve(ok);
        };

        const timer = setTimeout(() => finish(false), 5000);

        const sock = net.createConnection({ host, port }, () => {
            sock.write(`GET ${reqPath} HTTP/1.1\r\nHost: ${host}:${port}\r\nConnection: close\r\n\r\n`);
        });

        let response = Buffer.alloc(0);

        sock.on('data', chunk => { response = Buffer.concat([response, chunk]); });
        sock.on('error', () => finish(false));
        sock.on('close', () => {
            const text = response.toString('binary');
            const statusMatch = text.match(/^HTTP\/1\.[01]\s+(\d\d\d)/);
            if (!statusMatch) return finish(false);

            const status = parseInt(statusMatch[1], 10);
            if (status < 200 || status >= 300) return finish(false);

            const sepIdx = text.indexOf('\r\n\r\n');
            if (sepIdx !== -1) {
                const headers = text.slice(0, sepIdx);
                const bodyLen = response.length - (sepIdx + 4);
                const clMatch = headers.match(/Content-Length:\s*(\d+)/i);
                if (clMatch && bodyLen !== parseInt(clMatch[1], 10)) return finish(false);
            }

            finish(true);
        });
    });
}

async function runStressTest() {
    if (stressTestRunning) return;

    const files = collectWebRootFiles();
    if (!files.length) {
        showNotice('No files found in the web root to stress test.');
        return;
    }

    stressTestRunning = true;

    pushLogRecords(
        makeLine(''),
        makeLine(`${LABEL}Stress test started${RESET} ${MUTED}-${RESET} ${VALUE}${stressTestRate} req/s for ${stressTestDuration}s${RESET} against ${VALUE}${files.length} file(s)${RESET}`, 'center'),
        makeLine(''),
    );

    const rate = stressTestRate;
    const duration = stressTestDuration;
    const intervalMs = rate > 0 ? 1000 / rate : 1000;

    let sent = 0;
    let okCount = 0;
    const deadline = Date.now() + duration * 1000;
    const pending = [];

    while (Date.now() < deadline) {
        const file = files[Math.floor(Math.random() * files.length)];
        sent++;
        pending.push(httpGetOk(HOST, PORT, file).then(ok => { if (ok) okCount++; }));
        await sleep(intervalMs);
    }

    await Promise.all(pending);

    stressTestRunning = false;

    const passed = sent > 0 && okCount === sent;
    const pct = sent > 0 ? `${((okCount / sent) * 100).toFixed(1)}%` : '0%';

    pushLogRecords(
        makeLine(''),
        makeLine((passed ? `${GOOD}STRESS TEST PASSED` : `${BAD}STRESS TEST FAILED`) + RESET, 'center'),
        makeLine(`${MUTED}${okCount} / ${sent} requests succeeded (${pct})${RESET}`, 'center'),
        makeLine(''),
    );

    showNotice(
        passed ? 'Stress test PASSED' : 'Stress test FAILED',
        `${okCount} / ${sent} requests succeeded (${pct})`,
    );
}

const SECURITY_HEADERS = 'X-Content-Type-Options: nosniff\r\n' + 'X-Frame-Options: DENY\r\n';

// ======================
// Network access
// ======================

function bindHostFor(mode) {
    return mode === 'lan' ? '0.0.0.0' : '127.0.0.1';
}

// Best-guess LAN-reachable address for this machine: the first non-internal
// IPv4 address reported by the OS.
function detectLanIp() {
    const ifaces = os.networkInterfaces();
    for (const name of Object.keys(ifaces)) {
        for (const iface of ifaces[name] || []) {
            if (iface.family === 'IPv4' && !iface.internal) return iface.address;
        }
    }
    return undefined;
}

// The address to show the user for the current networkAccess mode.
function displayHost() {
    if (networkAccess !== 'lan') return '127.0.0.1';
    return lanIp || '0.0.0.0';
}

function refreshLanIp() {
    if (networkAccess !== 'lan') return;

    const now = Date.now();
    if (now - lastLanIpCheckAt < LAN_IP_CHECK_INTERVAL_MS) return;
    lastLanIpCheckAt = now;

    lanIp = detectLanIp();
}

// Close the current listener and rebind to the address for `mode`, trying
// the current port first and falling back the same way the startup bind
// does. Calls back with an Error on failure, leaving the live server untouched.
function applyNetworkAccess(mode, cb) {
    const newHost = bindHostFor(mode);
    if (newHost === HOST) return cb(null);

    const newServer = net.createServer(socket => handleClient(socket));
    let tryPort = PORT;
    let settled = false;

    newServer.on('error', err => {
        if (settled) return;

        if (err.code === 'EADDRINUSE' && tryPort < MAX_PORT) {
            tryPort++;
            newServer.listen(tryPort, newHost);
            return;
        }

        settled = true;
        newServer.removeAllListeners();
        try { newServer.close(); } catch (e) {}
        cb(err.code === 'EADDRINUSE' ? new Error(`No free ports available (tried ${PORT}-${MAX_PORT})`) : err);
    });

    newServer.on('listening', () => {
        settled = true;

        const oldServer = server;
        server = newServer;
        HOST = newHost;
        PORT = tryPort;
        networkAccess = mode;
        lanIp = mode === 'lan' ? detectLanIp() : undefined;

        try { oldServer.close(); } catch (e) {}

        pushLogRecords(
            makeLine(''),
            makeLine(`${LABEL}Network access changed${RESET} ${MUTED}-${RESET} now reachable at ${VALUE}http://${displayHost()}:${PORT}/${RESET}`, 'center'),
            makeLine(''),
        );

        cb(null);
    });

    newServer.listen(tryPort, newHost);
}

// ======================
// Socket setup
// ======================

loadSettings();
HOST = bindHostFor(networkAccess);
if (networkAccess === 'lan') lanIp = detectLanIp();

let server = net.createServer(socket => handleClient(socket));

server.on('error', err => {
    if (err.code === 'EADDRINUSE' && PORT < MAX_PORT) {
        process.stderr.write(`Port ${PORT} is in use, trying ${PORT + 1}...\n`);
        PORT++;
        server.listen(PORT, HOST);
        return;
    }

    if (err.code === 'EADDRINUSE') {
        process.stderr.write(`No free ports available (tried ${START_PORT}-${MAX_PORT})\n`);
    } else {
        process.stderr.write(`bind: ${err.message}\n`);
    }
    process.exit(1);
});

server.on('listening', () => {
    initHistory();
    rebuildToneWav();
    tuiInit();

    pushLogRecords(
        makeRule('#'),
        makeLine(`${LABEL}Server running at${RESET} ${VALUE}http://${displayHost()}:${PORT}/${RESET}`, 'center'),
        makeLine(`${LABEL}Web root:${RESET} ${VALUE}${REAL_WEB_ROOT}${RESET}`, 'center'),
        makeLine(`${LABEL}Listening for requests...${RESET}`, 'center'),
        makeLine(`${WARN}WARNING: For local development only!${RESET}`, 'center'),
        makeRule('#'),
        makeLine(''),
    );

    startTimers();
});

server.listen(PORT, HOST);

// ======================
// Main loop
// ======================

function startTimers() {
    setInterval(() => {
        cleanupOldLogs();
        wsCheckFilesystem();
        if (IS_TTY) requestRedraw();
    }, 1000).unref();

    setInterval(() => {
        if (redrawPending) flushRedraw();
    }, 20).unref();
}

function hasHeaderEnd(buf) {
    const s = buf.toString('binary');
    return s.includes('\r\n\r\n') || s.includes('\n\n');
}

function handleClient(client) {
    let clientIp = 'unknown';
    let buf = Buffer.alloc(0);
    let handled = false;

    client.setTimeout(SEND_STALL_TIMEOUT * 1000);

    const remote = client.remoteAddress;
    clientIp = remote ? remote.replace('::ffff:', '') : 'unknown';

    const readTimer = setTimeout(() => {
        if (handled) return;
        handled = true;
        sendResponse(client, 408, 'Request Timeout', 'text/plain', 'Timeout', 'unknown', undefined);
        client.end();
    }, READ_TIMEOUT * 1000);

    client.on('timeout', () => client.destroy());
    client.on('error', () => {});

    client.on('data', chunk => {
        if (handled) return;
        buf = Buffer.concat([buf, chunk]);

        if (buf.length >= MAX_REQUEST_SIZE && !hasHeaderEnd(buf)) {
            handled = true;
            clearTimeout(readTimer);
            sendResponse(client, 413, 'Request Entity Too Large', 'text/plain', 'Request too large', clientIp, undefined);
            client.end();
            return;
        }

        if (!hasHeaderEnd(buf)) return;

        handled = true;
        clearTimeout(readTimer);
        processRequest(client, buf, clientIp, keep => { if (!keep) client.end(); });
    });

    client.on('end', () => {
        if (handled) return;
        handled = true;
        clearTimeout(readTimer);
        if (buf.length === 0) return;
        processRequest(client, buf, clientIp, keep => { if (!keep) client.end(); });
    });
}

function escapeRe(str) {
    return str.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

function processRequest(client, buf, clientIp, cb) {
    const requestText = buf.toString('binary');

    const parsed = parseRequestLine(requestText);
    if (!parsed) {
        sendResponse(client, 400, 'Bad Request', 'text/plain', 'Invalid request', clientIp, undefined);
        return cb(false);
    }

    const { method, path: reqPath } = parsed;

    if (method !== 'GET') {
        sendResponse(client, 405, 'Method Not Allowed', 'text/plain', 'Method not allowed', clientIp, undefined);
        return cb(false);
    }

    if (/[^\x20-\x7E]/.test(reqPath)) {
        sendResponse(client, 400, 'Bad Request', 'text/plain', 'Invalid characters in path', clientIp, undefined);
        return cb(false);
    }

    if (HOT_RELOAD && new RegExp(`^${escapeRe(HOT_RELOAD_PATH)}(?:[?#]|$)`).test(reqPath)) {
        const headers = parseHeaders(requestText);

        if (/\bupgrade\b/i.test(headers['connection'] || '') &&
            (headers['upgrade'] || '').toLowerCase() === 'websocket' &&
            headers['sec-websocket-key'] !== undefined) {

            if (wsHandshake(client, headers['sec-websocket-key'])) {
                const c = { socket: client, ip: clientIp, buf: Buffer.alloc(0) };
                wsClients.push(c);
                if (lastWsSignature === undefined) lastWsSignature = webRootSignature();
                attachWsListeners(c);
                logWsConnect(clientIp);
                return cb(true);
            }
            return cb(false);
        }

        lastHotReload = formatTimestamp();
        lastPollEpoch = Math.floor(Date.now() / 1000);
        pollCount++;
        sendResponse(client, 200, 'OK', 'text/plain', webRootSignature(), clientIp, reqPath, { quiet: true });
        requestRedraw();
        return cb(false);
    }

    requestCount++;

    const filePath = sanitizePath(reqPath);
    if (!filePath) {
        sendResponse(client, 403, 'Forbidden', 'text/plain', 'Access denied', clientIp, reqPath);
        return cb(false);
    }

    serveFile(client, filePath, clientIp);
    return cb(false);
}

// ======================
// History persistence
// ======================

function historyFile() {
    return path.join(HISTORY_DIR, crypto.createHash('md5').update(REAL_WEB_ROOT).digest('hex') + '.hist');
}

function initHistory() {
    if (!fs.existsSync(HISTORY_DIR)) fs.mkdirSync(HISTORY_DIR, { recursive: true });
    loadHistory();
    historyReady = true;
}

function loadHistory() {
    const file = historyFile();
    if (!fs.existsSync(file)) return;

    let data;
    try { data = JSON.parse(fs.readFileSync(file, 'utf8')); } catch (e) { return; }
    if (!data || typeof data !== 'object') return;

    logLines = data.log_lines || [];
    streamCounter = data.stream_counter || 0;
    lastTime = data.last_time || (Math.floor(Date.now() / 1000) - 5);
    lastHotReload = data.last_hot_reload;
    lastPollEpoch = data.last_poll_epoch;
    pollCount = data.poll_count || 0;
    requestCount = data.request_count || 0;
    totalBytesSent = data.total_bytes_sent || 0;
    if (data.star_seed !== undefined) starSeed = data.star_seed;

    if (logLines.length > MAX_LOG_LINES) {
        logLines.splice(0, logLines.length - MAX_LOG_LINES);
    }
}

function saveHistory() {
    if (!historyReady || REAL_WEB_ROOT === undefined) return;

    if (!fs.existsSync(HISTORY_DIR)) fs.mkdirSync(HISTORY_DIR, { recursive: true });

    try {
        fs.writeFileSync(historyFile(), JSON.stringify({
            log_lines: logLines,
            stream_counter: streamCounter,
            last_time: lastTime,
            last_hot_reload: lastHotReload,
            last_poll_epoch: lastPollEpoch,
            poll_count: pollCount,
            request_count: requestCount,
            total_bytes_sent: totalBytesSent,
            star_seed: starSeed,
        }));
    } catch (e) { /* best-effort persistence */ }
}

function clearHistory() {
    logLines = [];
    scrollOffset = 0;
    streamCounter = 0;
    lastTime = Math.floor(Date.now() / 1000) - 5;
    lastHotReload = undefined;
    lastPollEpoch = undefined;
    pollCount = 0;
    requestCount = 0;
    totalBytesSent = 0;
    xferWindow = [];
    starSeed = Math.floor(Math.random() * 0x7FFFFFFF);

    try { fs.unlinkSync(historyFile()); } catch (e) {}

    pushLogRecords(makeLine(`${WARN}History cleared. Stream numbering restarts at #0.${RESET}`, 'center'));
}

// ======================
// Settings persistence
// ======================

function loadSettings() {
    if (!fs.existsSync(SETTINGS_FILE)) return;

    let data;
    try { data = JSON.parse(fs.readFileSync(SETTINGS_FILE, 'utf8')); } catch (e) { return; }
    if (!data || typeof data !== 'object') return;

    if (data.hot_reload !== undefined) HOT_RELOAD = data.hot_reload;
    if (data.hot_reload_mode !== undefined) HOT_RELOAD_MODE = data.hot_reload_mode === 'push' ? 'push' : 'poll';
    if (data.power_monitor_enabled !== undefined) powerMonitorEnabled = data.power_monitor_enabled;
    if (data.power_sample_interval !== undefined) POWER_SAMPLE_INTERVAL = data.power_sample_interval;
    if (data.xfer_window_secs !== undefined) XFER_WINDOW_SECS = data.xfer_window_secs;
    if (data.muted !== undefined) muted = data.muted;
    if ('kwh_cost' in data) kwhCost = data.kwh_cost;
    if (data.tone_volume !== undefined) toneVolume = data.tone_volume;
    if (data.stars_enabled !== undefined) starsEnabled = data.stars_enabled;
    if (data.star_density_scale !== undefined) starDensityScale = data.star_density_scale;
    if (data.star_colors_enabled !== undefined) starColorsEnabled = data.star_colors_enabled;
    if (data.stress_test_rate !== undefined) stressTestRate = data.stress_test_rate;
    if (data.stress_test_duration !== undefined) stressTestDuration = data.stress_test_duration;
    if (data.log_cleanup_enabled !== undefined) logCleanupEnabled = data.log_cleanup_enabled;
    if (data.log_max_age !== undefined) logMaxAge = data.log_max_age;
    if (data.target_fps !== undefined) targetFps = data.target_fps;
    if (data.network_access !== undefined) networkAccess = data.network_access === 'lan' ? 'lan' : 'local';
}

function saveSettings() {
    if (!fs.existsSync(HISTORY_DIR)) fs.mkdirSync(HISTORY_DIR, { recursive: true });

    try {
        fs.writeFileSync(SETTINGS_FILE, JSON.stringify({
            hot_reload: HOT_RELOAD,
            hot_reload_mode: HOT_RELOAD_MODE,
            power_monitor_enabled: powerMonitorEnabled,
            power_sample_interval: POWER_SAMPLE_INTERVAL,
            xfer_window_secs: XFER_WINDOW_SECS,
            muted,
            kwh_cost: kwhCost,
            tone_volume: toneVolume,
            stars_enabled: starsEnabled,
            star_density_scale: starDensityScale,
            star_colors_enabled: starColorsEnabled,
            stress_test_rate: stressTestRate,
            stress_test_duration: stressTestDuration,
            log_cleanup_enabled: logCleanupEnabled,
            log_max_age: logMaxAge,
            target_fps: targetFps,
            network_access: networkAccess,
        }));
    } catch (e) { /* best-effort persistence */ }
}

// ======================
// Terminal utility
// ======================

function startStreamBanner(streamMessage) {
    streamMessage = streamMessage.replace(/\x1b/g, '');

    pushLogRecords(
        makeLine(''),
        makeLine(''),
        makeRule('='),
        makeLine(LABEL + 'STARTING STREAM...' + RESET, 'center'),
        makeLine(VALUE + streamMessage + RESET, 'center'),
        makeRule('='),
        makeLine(''),
        makeLine(''),
    );

    playTone('stream');
}

function terminalSize() {
    if (!process.stdout.isTTY) return [24, 80];
    const rows = process.stdout.rows;
    const cols = process.stdout.columns;
    return (rows && cols) ? [rows, cols] : [24, 80];
}

function tuiInit() {
    if (!IS_TTY) return;

    if (process.stdin.isTTY) process.stdin.setRawMode(true);
    process.stdin.resume();

    process.on('SIGINT', () => process.exit(0));
    process.on('SIGTERM', () => process.exit(0));

    tuiActive = true;
    process.stdout.write('\x1b[?1049h\x1b[?25l\x1b[?7l\x1b[2J');
    requestRedraw();
}

function logHeight() {
    const height = TERM_ROWS - BAR_HEIGHT;
    return height < 1 ? 1 : height;
}

function clampScroll() {
    let max = logLines.length - logHeight();
    if (max < 0) max = 0;
    if (scrollOffset > max) scrollOffset = max;
    if (scrollOffset < 0) scrollOffset = 0;
}

function makeLine(text, align) {
    return { text: text || '', align: align || 'block' };
}

function makeRule(char) {
    return { rule: char };
}

function starFieldRow(row) {
    if (!starsEnabled) return '';

    let out = '';
    for (let layer = 0; layer < STAR_LAYERS.length; layer++) {
        const l = STAR_LAYERS[layer];
        const world = row - Math.floor(scrollOffset * l.speed);
        const hash = crypto.createHash('md5').update(`stars:${starSeed}:${layer}:${world}`).digest('hex');

        for (let i = 0; i < 3; i++) {
            const v = parseInt(hash.slice(i * 8, i * 8 + 8), 16);
            if ((v % 100) >= (l.density * starDensityScale)) continue;
            const col = (Math.floor(v / 100) % TERM_COLS) + 1;

            let color = starColorsEnabled
                ? l.colors[parseInt(hash.slice(28 + i, 29 + i), 16) % l.colors.length]
                : MUTED;

            const phase = v % 7;
            const bucket = Math.floor((Math.floor(Date.now() / 1000) + phase) / 3);
            const flareHash = crypto.createHash('md5').update(`twinkle:${starSeed}:${layer}:${world}:${i}:${bucket}`).digest('hex');
            const flare = parseInt(flareHash.slice(0, 8), 16) % 100;
            if (flare < 6) color = starColorsEnabled ? l.twinkle : VALUE;

            out += `\x1b[${row};${col}H${color}${l.char}${RESET}`;
        }
    }
    return out;
}

function redrawScreen() {
    if (!IS_TTY) return;

    const modalOpen = confirmOpen || noticeOpen || settingsOpen;

    const height = logHeight();
    const end = logLines.length - 1 - scrollOffset;
    const start = end - height + 1;

    let out = '';
    for (let row = 1; row <= height; row++) {
        out += `\x1b[${row};1H\x1b[0m\x1b[2K`;

        if (modalOpen) continue;

        const idx = start + row - 1;
        const rec = (idx >= 0 && idx <= end) ? logLines[idx] : undefined;

        if (rec && rec.rule) {
            out += FRAME + rec.rule.repeat(TERM_COLS) + RESET;
            continue;
        }

        out += starFieldRow(row);

        if (rec && rec.text && rec.text.length) {
            const width = rec.align === 'center' ? stripLen(rec.text) : LOG_WIDTH;
            let col = Math.floor((TERM_COLS - width) / 2) + 1;
            if (col < 1) col = 1;
            out += `\x1b[${row};${col}H${rec.text}`;
        }
    }

    out += drawStatusBar();
    out += drawConfirmBox();
    out += drawNoticeBox();
    out += drawSettingsBox();

    atomicPrint(out);

    lastRedrawAt = Date.now() / 1000;
    redrawPending = false;
}

function atomicPrint(content) {
    process.stdout.write(`\x1b[?2026h${content}\x1b[?2026l`);
}

function redrawInterval() {
    const fps = targetFps > 0 ? targetFps : 1;
    return 1 / fps;
}

function requestRedraw() {
    if (!IS_TTY) return;

    const now = Date.now() / 1000;
    if (now - lastRedrawAt >= redrawInterval()) {
        redrawScreen();
    } else {
        redrawPending = true;
    }
}

function flushRedraw() {
    const now = Date.now() / 1000;
    if (now - lastRedrawAt >= redrawInterval()) {
        redrawScreen();
    }
}

function stripLen(text) {
    return text.replace(/\x1b\[[0-9;]*m/g, '').length;
}

function barContent(left, right) {
    right = right || '';

    const inner = TERM_COLS - 2;
    let pad = inner - 2 - stripLen(left) - stripLen(right);
    if (pad < 1) pad = 1;

    return FRAME + '|' + RESET + ' ' + left + ' '.repeat(pad) + right + ' ' + FRAME + '|' + RESET;
}

function relativeAge(age) {
    if (age < 2) return 'just now';
    if (age < 60) return `${age}s ago`;
    return `${Math.floor(age / 60)}m ${age % 60}s ago`;
}

function drawStatusBar() {
    if (!IS_TTY) return '';

    samplePower();
    refreshLanIp();

    const inner = TERM_COLS - 2;

    let poll;
    if (HOT_RELOAD_MODE === 'push') {
        const n = wsClients.length;
        const dot = n > 0 ? `${GOOD}*${RESET}` : `${MUTED}o${RESET}`;
        const clientsStr = `${VALUE}${n}${RESET} ${MUTED}client${n === 1 ? '' : 's'}${RESET}`;
        if (lastWsReloadEpoch !== undefined) {
            const ageStr = relativeAge(Math.floor(Date.now() / 1000) - lastWsReloadEpoch);
            poll = `${dot} ${LABEL}Hot reload${RESET} ${MUTED}(WS)${RESET} ${clientsStr} `
                 + `${MUTED}- last push${RESET} ${VALUE}${lastWsReload}${RESET} `
                 + `${MUTED}(${ageStr})${RESET}`;
        } else {
            poll = `${dot} ${LABEL}Hot reload${RESET} ${MUTED}(WS)${RESET} ${clientsStr} `
                 + `${MUTED}- watching for changes${RESET}`;
        }
    } else if (lastPollEpoch !== undefined) {
        const age = Math.floor(Date.now() / 1000) - lastPollEpoch;
        const dotColor = age <= 3 ? GOOD : age <= 10 ? WARN : BAD;
        poll = `${dotColor}*${RESET} ${LABEL}Hot reload${RESET} `
             + `${MUTED}- last poll${RESET} ${VALUE}${lastHotReload}${RESET} `
             + `${MUTED}(${relativeAge(age)})${RESET}`;
    } else {
        poll = `${MUTED}o${RESET} ${LABEL}Hot reload${RESET} `
             + `${MUTED}- waiting for first poll...${RESET}`;
    }

    const title = `${LABEL}OVERPORT DEV SERVER${RESET}`;
    const url = `\x1b[4m${VALUE}http://${displayHost()}:${PORT}/${RESET}`;
    const counts = HOT_RELOAD_MODE === 'push'
        ? `${MUTED}pushes ${wsReloadCount} | reqs ${requestCount}${RESET}`
        : `${MUTED}polls ${pollCount} | reqs ${requestCount}${RESET}`;

    const xferRate = `${LABEL}Transfer${RESET} ${MUTED}-${RESET} ${VALUE}${formatDataSize(bytesPerWindow())}/min${RESET}`;
    const xferTotal = `${LABEL}Total sent${RESET} ${MUTED}-${RESET} ${VALUE}${formatDataSize(totalBytesSent)}${RESET}`;

    let powerValue;
    if (!powerMonitorEnabled) {
        powerValue = `${MUTED}Disabled${RESET}`;
    } else if (powerWatts !== undefined) {
        powerValue = `${VALUE}${powerWatts.toFixed(1)} W${RESET}`;
    } else {
        const stuck = !powerEverOk && (Math.floor(Date.now() / 1000) - SERVER_START_TIME) >= POWER_ROOT_HINT_AFTER;
        powerValue = `${MUTED}N/A${RESET}` + (stuck ? ` ${WARN}(try running as root)${RESET}` : '');
    }
    const power = `${LABEL}Power draw${RESET} ${MUTED}-${RESET} ${powerValue}`;
    let powerMeta = powerSource !== undefined ? `${MUTED}via ${powerSource}${RESET}` : '';
    if (powerWatts !== undefined && kwhCost !== undefined) {
        const costPerHr = (powerWatts / 1000) * kwhCost;
        powerMeta += (powerMeta !== '' ? '  ' : '') + `${MUTED}~$${formatCost(costPerHr)}/hr${RESET}`;
    }

    const keys = `${MUTED}Scroll: Up/Dn PgUp/PgDn Home End | o open | c clear | m mute | s settings | t stress | q quit${RESET}`;
    let mode = scrollOffset > 0
        ? `${WARN}^ SCROLLED +${scrollOffset}${RESET}`
        : `${GOOD}>> FOLLOWING${RESET}`;
    mode += '  ' + ((muted || toneVolume === 0) ? `${MUTED}- muted${RESET}` : `${GOOD}- sound${RESET}`);

    const rows = [
        FRAME + '+' + '-'.repeat(inner) + '+' + RESET,
        barContent(title, url),
        barContent(poll, counts),
        barContent(xferRate, xferTotal),
        barContent(power, powerMeta),
        barContent(keys, mode),
        FRAME + '+' + '-'.repeat(inner) + '+' + RESET,
    ];

    const top = TERM_ROWS - BAR_HEIGHT + 1;
    let out = '';
    for (let i = 0; i < rows.length; i++) {
        const row = top + i;
        out += `\x1b[${row};1H\x1b[0m\x1b[2K${rows[i]}`;
    }
    return out;
}

function boxRow(content, inner) {
    const vis = stripLen(content);
    let padl = Math.floor((inner - vis) / 2);
    if (padl < 0) padl = 0;
    let padr = inner - vis - padl;
    if (padr < 0) padr = 0;

    return `${WARN}|${RESET}` + ' '.repeat(padl) + content + ' '.repeat(padr) + `${WARN}|${RESET}`;
}

function drawConfirmBox() {
    if (!IS_TTY || !confirmOpen) return '';

    let w = 50;
    if (w > TERM_COLS) w = TERM_COLS;
    const inner = w - 2;

    let left = Math.floor((TERM_COLS - w) / 2) + 1;
    if (left < 1) left = 1;

    const yes = confirmChoice === 1 ? `${WARN}\x1b[7m [ Yes ] ${RESET}` : `${MUTED} [ Yes ] ${RESET}`;
    const no = confirmChoice === 0 ? `${GOOD}\x1b[7m [ No ] ${RESET}` : `${MUTED} [ No ] ${RESET}`;

    const border = WARN + '+' + '-'.repeat(inner) + '+' + RESET;
    const lines = [
        border,
        boxRow('', inner),
        boxRow(`${VALUE}Clear saved history for this web root?${RESET}`, inner),
        boxRow(`${MUTED}Stream numbering will restart at #0.${RESET}`, inner),
        boxRow('', inner),
        boxRow(yes + '    ' + no, inner),
        boxRow('', inner),
        border,
    ];

    let top = Math.floor((logHeight() - lines.length) / 2) + 1;
    if (top < 1) top = 1;

    let out = '';
    for (let i = 0; i < lines.length; i++) {
        const row = top + i;
        out += `\x1b[${row};${left}H\x1b[0m${lines[i]}`;
    }
    return out;
}

function drawNoticeBox() {
    if (!IS_TTY || !noticeOpen) return '';

    let w = 60;
    if (w > TERM_COLS) w = TERM_COLS;
    const inner = w - 2;

    let left = Math.floor((TERM_COLS - w) / 2) + 1;
    if (left < 1) left = 1;

    const border = WARN + '+' + '-'.repeat(inner) + '+' + RESET;
    const lines = [border, boxRow('', inner)];
    for (const t of noticeText) lines.push(boxRow(`${VALUE}${t}${RESET}`, inner));
    lines.push(boxRow('', inner));
    lines.push(boxRow(`${MUTED}Press any key to dismiss${RESET}`, inner));
    lines.push(boxRow('', inner));
    lines.push(border);

    let top = Math.floor((logHeight() - lines.length) / 2) + 1;
    if (top < 1) top = 1;

    let out = '';
    for (let i = 0; i < lines.length; i++) {
        const row = top + i;
        out += `\x1b[${row};${left}H\x1b[0m${lines[i]}`;
    }
    return out;
}

function showNotice(...lines) {
    noticeText = lines;
    noticeOpen = true;
    requestRedraw();
}

function handleNoticeKeys() {
    noticeOpen = false;
    requestRedraw();
}

function handleConfirmKeys(buf) {
    while (buf.length) {
        let m;
        if ((m = buf.match(/^(?:\x1b\[[ABCD]|\x1bO[ABCD])/))) {
            confirmChoice = 1 - confirmChoice;
            requestRedraw();
            buf = buf.slice(m[0].length);
        } else if ((m = buf.match(/^[\r\n]/))) {
            const confirmed = confirmChoice === 1;
            confirmOpen = false;
            if (confirmed) {
                clearHistory();
            } else {
                requestRedraw();
            }
            return;
        } else if ((m = buf.match(/^\x1b/))) {
            confirmOpen = false;
            requestRedraw();
            return;
        } else {
            buf = buf.slice(1);
        }
    }
}

function cycleValue(current, direction, steps) {
    for (let i = 0; i < steps.length; i++) {
        if (steps[i] === current) {
            return steps[(i + direction + steps.length) % steps.length];
        }
    }
    return steps[0];
}

function humanizeDuration(secs) {
    const YEAR = 365 * 86400;

    if (secs < 60) return `${secs}s`;

    const mins = secs / 60;
    if (secs < 3600) return `${Math.floor(mins)}m`;

    const hours = secs / 3600;
    if (secs < 86400) return `${Math.floor(hours)}h`;

    const days = secs / 86400;
    if (secs < YEAR) return `${Math.floor(days)}d`;

    const years = secs / YEAR;
    if (secs < 10 * YEAR) return `${Math.floor(years)}y`;

    const decades = secs / (10 * YEAR);
    if (secs < 100 * YEAR) return `${Math.floor(decades)} decade${Math.floor(decades) === 1 ? '' : 's'}`;

    const centuries = secs / (100 * YEAR);
    if (secs < 1000 * YEAR) return `${Math.floor(centuries)} centur${Math.floor(centuries) === 1 ? 'y' : 'ies'}`;

    const millennia = secs / (1000 * YEAR);
    return `${Math.floor(millennia)} millenni${Math.floor(millennia) === 1 ? 'um' : 'a'}`;
}

function settingsList() {
    return [
        {
            category: 'Development', label: 'Hot reload',
            render: () => HOT_RELOAD ? 'Enabled' : 'Disabled',
            toggle: () => { HOT_RELOAD = !HOT_RELOAD; },
        },
        {
            category: 'Development', label: 'Hot reload mode',
            render: () => HOT_RELOAD_MODE === 'push' ? 'WebSocket (push)' : 'Poll (fetch)',
            toggle: () => {
                HOT_RELOAD_MODE = HOT_RELOAD_MODE === 'push' ? 'poll' : 'push';
                settingsFlash = 'Refresh open pages to apply the new mode.';
            },
        },
        {
            category: 'Development', label: 'Network access',
            render: () => networkAccess === 'lan' ? 'LAN (all interfaces)' : 'Local only',
            toggle: () => {
                const newMode = networkAccess === 'lan' ? 'local' : 'lan';
                applyNetworkAccess(newMode, err => {
                    if (err) {
                        settingsFlash = `Could not switch: ${err.message}`;
                    } else {
                        settingsFlash = `Now reachable at http://${displayHost()}:${PORT}/`;
                        saveSettings();
                    }
                    requestRedraw();
                });
            },
        },
        {
            category: 'Development', label: 'Stress test rate',
            render: () => `${stressTestRate} req/s`,
            toggle: dir => { stressTestRate = cycleValue(stressTestRate, dir, [1, 5, 10, 25, 50, 100, 200]); },
        },
        {
            category: 'Development', label: 'Stress test duration',
            render: () => humanizeDuration(stressTestDuration),
            toggle: dir => { stressTestDuration = cycleValue(stressTestDuration, dir, [5, 10, 30, 60, 120, 300]); },
        },
        {
            category: 'Development', label: 'Auto log cleanup',
            render: () => logCleanupEnabled ? 'Enabled' : 'Disabled',
            toggle: () => { logCleanupEnabled = !logCleanupEnabled; },
        },
        {
            category: 'Development', label: 'Log max age',
            render: () => humanizeDuration(logMaxAge),
            toggle: dir => {
                logMaxAge = cycleValue(logMaxAge, dir, [
                    300, 900, 1800, 3600, 21600, 43200,
                    86400, 259200, 604800, 2592000, 7776000, 31536000,
                    63072000, 126144000, 157680000,
                    315360000, 3153600000, 31536000000,
                ]);
            },
        },
        {
            category: 'Estimations', label: 'Power monitor',
            render: () => powerMonitorEnabled ? 'Enabled' : 'Disabled',
            toggle: () => {
                powerMonitorEnabled = !powerMonitorEnabled;
                if (!powerMonitorEnabled) {
                    powerWatts = undefined;
                    powerSource = undefined;
                }
            },
        },
        {
            category: 'Estimations', label: 'Power sample rate',
            render: () => `every ${POWER_SAMPLE_INTERVAL}s`,
            toggle: dir => { POWER_SAMPLE_INTERVAL = cycleValue(POWER_SAMPLE_INTERVAL, dir, [2, 5, 10, 30, 60]); },
        },
        {
            category: 'Estimations', label: 'Bandwidth window',
            render: () => `${XFER_WINDOW_SECS}s`,
            toggle: dir => { XFER_WINDOW_SECS = cycleValue(XFER_WINDOW_SECS, dir, [15, 30, 60, 120, 300]); },
        },
        {
            category: 'Estimations', label: 'Cost per kWh', type: 'text',
            render: () => kwhCost !== undefined ? `$${kwhCost.toFixed(4)}` : 'not set',
            editInit: () => kwhCost !== undefined ? kwhCost.toFixed(4) : '',
            commit: text => {
                if (text === '') kwhCost = undefined;
                else if (/^\d*\.?\d+$/.test(text)) kwhCost = parseFloat(text);
            },
        },
        {
            category: 'Cosmetics', label: 'Sound',
            render: () => muted ? 'Muted' : 'Enabled',
            toggle: () => { muted = !muted; },
        },
        {
            category: 'Cosmetics', label: 'Tone volume',
            render: () => `${Math.round(toneVolume * 100)}%`,
            toggle: dir => {
                toneVolume = cycleValue(toneVolume, dir, [0, 0.25, 0.5, 0.75, 1, 1.25, 1.5]);
                rebuildToneWav();
            },
        },
        {
            category: 'Cosmetics', label: 'Stars',
            render: () => starsEnabled ? 'Enabled' : 'Disabled',
            toggle: () => { starsEnabled = !starsEnabled; },
        },
        {
            category: 'Cosmetics', label: 'Star frequency',
            render: () => `${Math.round(starDensityScale * 100)}%`,
            toggle: dir => { starDensityScale = cycleValue(starDensityScale, dir, [0.25, 0.5, 1, 1.5, 2]); },
        },
        {
            category: 'Cosmetics', label: 'Star colors',
            render: () => starColorsEnabled ? 'Colored' : 'Monochrome',
            toggle: () => { starColorsEnabled = !starColorsEnabled; },
        },
        {
            category: 'Cosmetics', label: 'Frame rate',
            render: () => `${targetFps} fps`,
            toggle: dir => { targetFps = cycleValue(targetFps, dir, [1, 2, 5, 10, 15, 20, 30, 60]); },
        },
    ];
}

function drawSettingsBox() {
    if (!IS_TTY || !settingsOpen) return '';

    const settings = settingsList();

    let w = 56;
    if (w > TERM_COLS) w = TERM_COLS;
    const inner = w - 2;

    let left = Math.floor((TERM_COLS - w) / 2) + 1;
    if (left < 1) left = 1;

    const border = WARN + '+' + '-'.repeat(inner) + '+' + RESET;
    let lines = [
        border,
        boxRow(`${LABEL}SETTINGS${RESET}`, inner),
        border,
    ];

    const values = [];
    let labelWidth = 0;
    let valueWidth = 0;
    for (let i = 0; i < settings.length; i++) {
        let value = settings[i].render();
        if (settingsEditing && i === settingsIndex) value = settingsEditBuffer + '_';
        values[i] = String(value);

        if (settings[i].label.length > labelWidth) labelWidth = settings[i].label.length;
        if (values[i].length > valueWidth) valueWidth = values[i].length;
    }

    let category = '';
    for (let i = 0; i < settings.length; i++) {
        const s = settings[i];

        if (s.category !== category) {
            category = s.category;
            if (i > 0) lines.push(boxRow('', inner));
            lines.push(boxRow(`${MUTED}-- ${category} --${RESET}`, inner));
        }

        const label = s.label.padEnd(labelWidth);
        const value = values[i].padStart(valueWidth);

        const rowContent = i === settingsIndex
            ? `${WARN}\x1b[7m ${label}  ${value} ${RESET}`
            : ` ${LABEL}${label}${RESET}  ${VALUE}${value}${RESET} `;

        lines.push(boxRow(rowContent, inner));
    }

    if (settingsFlash.length) {
        lines.push(boxRow('', inner));
        lines.push(boxRow(`${WARN}! ${settingsFlash}${RESET}`, inner));
    }

    lines.push(border);
    if (settingsEditing) {
        lines.push(boxRow(`${MUTED}Type digits and '.' | Backspace delete${RESET}`, inner));
        lines.push(boxRow(`${MUTED}Enter confirm | Esc cancel${RESET}`, inner));
    } else {
        lines.push(boxRow(`${MUTED}Up/Dn select | Left back | Right/Space forward${RESET}`, inner));
        lines.push(boxRow(`${MUTED}s or Esc to close${RESET}`, inner));
    }
    lines.push(border);

    let top = Math.floor((logHeight() - lines.length) / 2) + 1;
    if (top < 1) top = 1;

    let out = '';
    for (let i = 0; i < lines.length; i++) {
        const row = top + i;
        out += `\x1b[${row};${left}H\x1b[0m${lines[i]}`;
    }
    return out;
}

function handleSettingsKeys(buf) {
    if (settingsEditing) return handleSettingsEditKeys(buf);

    const settings = settingsList();

    while (buf.length) {
        let m;
        if ((m = buf.match(/^(?:\x1b\[A|\x1bOA)/))) {
            settingsIndex = (settingsIndex - 1 + settings.length) % settings.length;
            requestRedraw();
            buf = buf.slice(m[0].length);
        } else if ((m = buf.match(/^(?:\x1b\[B|\x1bOB)/))) {
            settingsIndex = (settingsIndex + 1) % settings.length;
            requestRedraw();
            buf = buf.slice(m[0].length);
        } else if ((m = buf.match(/^(?:\x1b\[D|\x1bOD)/))) {
            const s = settings[settingsIndex];
            if ((s.type || '') !== 'text') {
                s.toggle(-1);
                saveSettings();
                requestRedraw();
            }
            buf = buf.slice(m[0].length);
        } else if ((m = buf.match(/^(?:\x1b\[C|\x1bOC| )/))) {
            const s = settings[settingsIndex];
            if ((s.type || '') === 'text') {
                settingsEditBuffer = s.editInit();
                settingsEditing = true;
                requestRedraw();
            } else {
                s.toggle(1);
                saveSettings();
                requestRedraw();
            }
            buf = buf.slice(m[0].length);
        } else if ((m = buf.match(/^[\r\n]/))) {
            const s = settings[settingsIndex];
            if ((s.type || '') === 'text') {
                settingsEditBuffer = s.editInit();
                settingsEditing = true;
                requestRedraw();
            }
            buf = buf.slice(m[0].length);
        } else if ((m = buf.match(/^[sS\x1b]/))) {
            settingsOpen = false;
            settingsFlash = '';
            requestRedraw();
            return;
        } else {
            buf = buf.slice(1);
        }
    }
}

function handleSettingsEditKeys(buf) {
    const settings = settingsList();
    const s = settings[settingsIndex];

    while (buf.length) {
        let m;
        if ((m = buf.match(/^[0-9.]/))) {
            if (!(m[0] === '.' && settingsEditBuffer.indexOf('.') >= 0)) settingsEditBuffer += m[0];
            requestRedraw();
            buf = buf.slice(1);
        } else if ((m = buf.match(/^(?:\x7f|\x08)/))) {
            if (settingsEditBuffer.length) settingsEditBuffer = settingsEditBuffer.slice(0, -1);
            requestRedraw();
            buf = buf.slice(m[0].length);
        } else if ((m = buf.match(/^[\r\n]/))) {
            s.commit(settingsEditBuffer);
            settingsEditing = false;
            saveSettings();
            requestRedraw();
            buf = buf.slice(m[0].length);
        } else if ((m = buf.match(/^\x1b/))) {
            settingsEditing = false;
            requestRedraw();
            buf = buf.slice(m[0].length);
        } else {
            buf = buf.slice(1);
        }
    }
}

function browserLaunchCommand(url) {
    if (process.env.BROWSER) return [process.env.BROWSER, url];

    if (process.platform === 'darwin') return ['open', url];
    if (process.platform === 'win32') return ['cmd', '/c', 'start', '""', url];
    if (process.platform === 'linux') return ['xdg-open', url];

    return [];
}

function openBrowser() {
    // Always target loopback here: 0.0.0.0 isn't a browsable address, and
    // the machine running this command can always reach itself via it.
    const url = `http://127.0.0.1:${PORT}/`;
    const launcher = browserLaunchCommand(url);

    if (!launcher.length) {
        const message = [
            `Automatic browser launch isn't supported on this OS (${process.platform}).`,
            `Open ${url} manually in your browser.`,
        ];
        if (IS_TTY) {
            showNotice(...message);
        } else {
            for (const m of message) pushLogRecords(makeLine(`${WARN}${m}${RESET}`, 'center'));
        }
        return;
    }

    const [cmd, ...args] = launcher;
    const { env, uid, gid } = childEnvAndIds();

    try {
        const child = spawn(cmd, args, { stdio: 'ignore', env, uid, gid, detached: true });
        child.on('error', () => {});
        child.unref();
    } catch (e) { /* best-effort browser launch */ }

    logOutput(browserOpenedBanner(url), 'center');
    playTone('browser');
}

function handleKeys(chunk) {
    let buf = chunk.toString('binary');
    if (!buf.length) return;

    if (noticeOpen) return handleNoticeKeys();
    if (confirmOpen) return handleConfirmKeys(buf);
    if (settingsOpen) return handleSettingsKeys(buf);

    let page = logHeight() - 1;
    if (page < 1) page = 1;
    const before = scrollOffset;

    while (buf.length) {
        let m;
        if ((m = buf.match(/^\x1b\[5~/))) { scrollOffset += page; buf = buf.slice(m[0].length); }
        else if ((m = buf.match(/^\x1b\[6~/))) { scrollOffset -= page; buf = buf.slice(m[0].length); }
        else if ((m = buf.match(/^(?:\x1b\[A|\x1bOA)/))) { scrollOffset += 1; buf = buf.slice(m[0].length); }
        else if ((m = buf.match(/^(?:\x1b\[B|\x1bOB)/))) { scrollOffset -= 1; buf = buf.slice(m[0].length); }
        else if ((m = buf.match(/^(?:\x1b\[H|\x1b\[1~|\x1bOH)/))) { scrollOffset = logLines.length; buf = buf.slice(m[0].length); }
        else if ((m = buf.match(/^(?:\x1b\[F|\x1b\[4~|\x1bOF)/))) { scrollOffset = 0; buf = buf.slice(m[0].length); }
        else if (buf[0] === '\x03') { process.exit(0); }
        else if (buf[0] === 'o') { openBrowser(); buf = buf.slice(1); }
        else if (buf[0] === 'c') {
            confirmOpen = true;
            confirmChoice = 0;
            requestRedraw();
            return;
        }
        else if (buf[0] === 'm' || buf[0] === 'M') {
            muted = !muted;
            saveSettings();
            requestRedraw();
            buf = buf.slice(1);
        }
        else if (buf[0] === 's' || buf[0] === 'S') {
            settingsOpen = true;
            settingsIndex = 0;
            settingsFlash = '';
            requestRedraw();
            return;
        }
        else if (buf[0] === 't' || buf[0] === 'T') { runStressTest(); buf = buf.slice(1); }
        else if (buf[0] === 'q') { process.exit(0); }
        else { buf = buf.slice(1); }
    }

    clampScroll();
    if (scrollOffset !== before) requestRedraw();
}

if (IS_TTY && process.stdin.isTTY) {
    process.stdin.on('data', chunk => handleKeys(chunk));
}

if (IS_TTY) {
    process.stdout.on('resize', () => {
        [TERM_ROWS, TERM_COLS] = terminalSize();
        clampScroll();
        requestRedraw();
    });
}

function cleanupOldLogs() {
    if (!logCleanupEnabled) return;

    const cutoff = Math.floor(Date.now() / 1000) - logMaxAge;
    let removed = 0;

    while (logLines.length && (logLines[0].time || 0) < cutoff) {
        logLines.shift();
        removed++;
    }

    if (removed) clampScroll();
}

function pushLogRecords(...records) {
    const now = Math.floor(Date.now() / 1000);
    for (const r of records) r.time = now;

    logLines.push(...records);
    if (scrollOffset > 0) scrollOffset += records.length;

    if (logLines.length > MAX_LOG_LINES) {
        logLines.splice(0, logLines.length - MAX_LOG_LINES);
    }

    cleanupOldLogs();

    if (!IS_TTY) {
        for (const rec of records) {
            if (rec.rule) {
                process.stdout.write(FRAME + rec.rule.repeat(LOG_WIDTH) + RESET + '\n');
            } else {
                process.stdout.write(rec.text + '\n');
            }
        }
        return;
    }

    clampScroll();
    requestRedraw();
}

function logOutput(content, align) {
    const lines = content.split('\n');
    if (lines.length && lines[lines.length - 1] === '') lines.pop();
    pushLogRecords(...lines.map(l => makeLine(l, align)));
}

// ======================
// Request parsing
// ======================

function uriUnescape(str) {
    const bytes = [];
    for (let i = 0; i < str.length; i++) {
        if (str[i] === '%' && /^[0-9A-Fa-f]{2}$/.test(str.slice(i + 1, i + 3))) {
            bytes.push(parseInt(str.slice(i + 1, i + 3), 16));
            i += 2;
        } else {
            bytes.push(str.charCodeAt(i) & 0xff);
        }
    }
    return Buffer.from(bytes).toString('utf8');
}

function parseRequestLine(request) {
    const m = request.match(/^([A-Z]+)\s+(\S+)\s+HTTP\/1\.[01]\r?\n/);
    if (!m) return null;

    const method = m[1];
    const decoded = uriUnescape(m[2]);
    if (decoded.includes('\0')) return null;

    return { method, path: decoded };
}

// ======================
// Path sanitization
// ======================

function pathWithinRoot(p) {
    if (p === undefined) return false;
    if (p === REAL_WEB_ROOT) return true;
    return p.indexOf(ROOT_PREFIX) === 0;
}

function sanitizePath(reqPath) {
    let p = (reqPath === undefined || reqPath === '') ? '/' : reqPath;

    p = p.replace(/[?#].*$/, '');
    p = p.replace(/\\/g, '/');
    p = p.replace(/\/+/g, '/');

    if (p.includes('..')) return undefined;

    const fullPath = path.join(REAL_WEB_ROOT, p);

    let realPath;
    try { realPath = fs.realpathSync(fullPath); } catch (e) { realPath = undefined; }

    if (!realPath) {
        const components = p.split('/');
        let depth = 0;
        for (const comp of components) {
            if (comp === '..') {
                depth--;
                if (depth < 0) return undefined;
            } else if (comp !== '.' && comp !== '') {
                depth++;
            }
        }
        realPath = fullPath;
    }

    if (!pathWithinRoot(realPath)) return undefined;

    const relativePath = realPath.slice(REAL_WEB_ROOT.length);
    if (/\/\./.test(relativePath) || relativePath.startsWith('.')) return undefined;

    let isDir = false;
    try { isDir = fs.statSync(realPath).isDirectory(); } catch (e) { /* not present */ }

    if (isDir) return INDEX_FILE;

    return realPath;
}

// ======================
// Hot reload
// ======================

function webRootSignature() {
    const entries = [];

    let rootSt;
    try {
        rootSt = fs.lstatSync(REAL_WEB_ROOT);
        entries.push(`${REAL_WEB_ROOT}|${Math.floor(rootSt.mtimeMs / 1000)}|${rootSt.size}`);
    } catch (e) { /* web root vanished mid-scan */ }

    function walk(dir) {
        let list;
        try { list = fs.readdirSync(dir, { withFileTypes: true }); } catch (e) { return; }
        for (const entry of list) {
            const full = path.join(dir, entry.name);
            let st;
            try { st = fs.lstatSync(full); } catch (e) { continue; }
            entries.push(`${full}|${Math.floor(st.mtimeMs / 1000)}|${st.size}`);
            if (entry.isDirectory()) walk(full);
        }
    }
    walk(REAL_WEB_ROOT);

    entries.sort();
    return crypto.createHash('md5').update(entries.join('\n')).digest('hex');
}

// The snippet injected before </body>. In poll mode the browser drives the
// check by fetching the signature; in push mode it opens a WebSocket and waits
// for the server to tell it when to reload.
function hotReloadScript() {
    if (HOT_RELOAD_MODE === 'push') {
        return `<script>
(function () {
    var proto = location.protocol === 'https:' ? 'wss://' : 'ws://';
    var url = proto + location.host + '${HOT_RELOAD_PATH}';
    function connect() {
        var ws;
        try { ws = new WebSocket(url); }
        catch (e) { setTimeout(connect, ${HOT_RELOAD_POLL_MS}); return; }
        ws.onmessage = function (ev) {
            if (ev.data === 'reload') location.reload();
        };
        ws.onclose = function () { setTimeout(connect, ${HOT_RELOAD_POLL_MS}); };
        ws.onerror = function () { try { ws.close(); } catch (e) {} };
    }
    connect();
})();
</script>
`;
    }

    return `<script>
(function () {
    var current = null;
    function poll() {
        fetch('${HOT_RELOAD_PATH}', { cache: 'no-store' })
            .then(function (res) { return res.text(); })
            .then(function (sig) {
                if (current === null) {
                    current = sig;
                } else if (sig !== current) {
                    location.reload();
                    return;
                }
                setTimeout(poll, ${HOT_RELOAD_POLL_MS});
            })
            .catch(function () { setTimeout(poll, ${HOT_RELOAD_POLL_MS}); });
    }
    poll();
})();
</script>
`;
}

// ======================
// WebSocket push transport (RFC 6455, subset)
// ======================

// Split a raw HTTP request into a lowercased-name => value header map.
function parseHeaders(request) {
    const h = {};
    const lines = request.split(/\r?\n/);
    lines.shift(); // drop the request line

    for (const line of lines) {
        if (line === '') break;
        const m = line.match(/^([^:]+):\s*(.*?)\s*$/);
        if (m) h[m[1].toLowerCase()] = m[2];
    }

    return h;
}

// Complete the opening handshake. Returns true on success.
function wsHandshake(client, key) {
    const accept = crypto.createHash('sha1').update(key + WS_GUID).digest('base64');

    const response =
        'HTTP/1.1 101 Switching Protocols\r\n' +
        'Upgrade: websocket\r\n' +
        'Connection: Upgrade\r\n' +
        `Sec-WebSocket-Accept: ${accept}\r\n\r\n`;

    try { client.write(response); } catch (e) { return false; }
    recordTransfer(Buffer.byteLength(response));
    return true;
}

// Encode a server->client text frame (unmasked, per spec).
function wsEncodeText(payload) {
    const payloadBuf = Buffer.from(payload, 'utf8');
    const len = payloadBuf.length;

    let header;
    if (len < 126) {
        header = Buffer.from([0x81, len]);
    } else if (len < 65536) {
        header = Buffer.alloc(4);
        header[0] = 0x81; header[1] = 126;
        header.writeUInt16BE(len, 2);
    } else {
        header = Buffer.alloc(10);
        header[0] = 0x81; header[1] = 127;
        header.writeUInt32BE(0, 2);
        header.writeUInt32BE(len, 6);
    }

    return Buffer.concat([header, payloadBuf]);
}

// Drop a connection and re-baseline the monitor once the last client leaves.
function wsRemoveClient(c) {
    wsClients = wsClients.filter(x => x !== c);
    try { c.socket.destroy(); } catch (e) {}

    if (!wsClients.length) lastWsSignature = undefined;
    requestRedraw();
}

function attachWsListeners(c) {
    c.socket.on('data', chunk => {
        c.buf = Buffer.concat([c.buf, chunk]);
        wsHandleReadable(c);
    });
    c.socket.on('close', () => wsRemoveClient(c));
    c.socket.on('error', () => {});
}

// Consume whatever the client sent: honor close frames, answer pings, and
// ignore everything else (text/binary/pong payloads).
function wsHandleReadable(c) {
    while (true) {
        const buf = c.buf;
        if (buf.length < 2) return;

        const b0 = buf[0];
        const b1 = buf[1];
        const opcode = b0 & 0x0f;
        const masked = (b1 & 0x80) !== 0;
        let len = b1 & 0x7f;
        let offset = 2;

        if (len === 126) {
            if (buf.length < 4) return;
            len = buf.readUInt16BE(2);
            offset = 4;
        } else if (len === 127) {
            if (buf.length < 10) return;
            len = buf.readUInt32BE(6); // dev payloads never approach 4 GiB
            offset = 10;
        }

        const maskLen = masked ? 4 : 0;
        if (buf.length < offset + maskLen + len) return;

        const mask = masked ? buf.subarray(offset, offset + 4) : null;
        let payload = buf.subarray(offset + maskLen, offset + maskLen + len);

        if (masked) {
            const out = Buffer.alloc(payload.length);
            for (let i = 0; i < payload.length; i++) out[i] = payload[i] ^ mask[i % 4];
            payload = out;
        }

        c.buf = Buffer.from(buf.subarray(offset + maskLen + len));

        if (opcode === 0x8) { // close
            try { c.socket.write(Buffer.from([0x88, 0])); } catch (e) {}
            wsRemoveClient(c);
            return;
        } else if (opcode === 0x9) { // ping -> pong (control payloads are < 126 bytes)
            try { c.socket.write(Buffer.concat([Buffer.from([0x8A, payload.length]), payload])); } catch (e) {}
        }
        // text / binary / pong: nothing to do
    }
}

// Tell every connected client to reload, pruning any that have gone away.
function wsBroadcastReload() {
    const frame = wsEncodeText('reload');

    const survivors = [];
    for (const c of wsClients) {
        try {
            c.socket.write(frame);
            survivors.push(c);
        } catch (e) {
            try { c.socket.destroy(); } catch (e2) {}
        }
    }
    wsClients = survivors;

    wsReloadCount++;
    lastWsReload = formatTimestamp();
    lastWsReloadEpoch = Math.floor(Date.now() / 1000);

    const n = wsClients.length;
    pushLogRecords(
        makeLine(`${GOOD}>> Hot reload pushed${RESET} ${MUTED}- ${n} client${n === 1 ? '' : 's'} notified${RESET}`, 'center'),
    );
    playTone('browser');
}

// While clients are connected, watch the web root and push a reload on change.
function wsCheckFilesystem() {
    if (!wsClients.length) return;

    const now = Date.now();
    if (now - lastWsScanAt < WS_SCAN_INTERVAL_MS) return;
    lastWsScanAt = now;

    const sig = webRootSignature();

    if (lastWsSignature === undefined) {
        lastWsSignature = sig;
        return;
    }

    if (sig === lastWsSignature) return;

    lastWsSignature = sig;
    wsBroadcastReload();
}

function logWsConnect(ip) {
    const n = wsClients.length;
    pushLogRecords(
        makeLine(`${GOOD}o${RESET} ${LABEL}Hot reload client connected${RESET} ${MUTED}(${ip}) - ${n} active${RESET}`, 'center'),
    );
}

// ======================
// File serving
// ======================

function serveFile(client, filePath, clientIp) {
    if (!pathWithinRoot(filePath)) return serve403(client, clientIp, filePath);

    let stat;
    try { stat = fs.statSync(filePath); } catch (e) { return serve404(client, clientIp, filePath); }
    if (!stat.isFile()) return serve404(client, clientIp, filePath);
    try { fs.accessSync(filePath, fs.constants.R_OK); } catch (e) { return serve404(client, clientIp, filePath); }

    serveStatic(client, filePath, clientIp, 200, 'OK');
}

function serveStatic(client, filePath, clientIp, code, status) {
    const extMatch = filePath.match(/\.([^.]+)$/);
    const ext = extMatch ? extMatch[1].toLowerCase() : '';
    const mimeType = MIME_TYPES[ext] || 'application/octet-stream';

    let fileBuf;
    try { fileBuf = fs.readFileSync(filePath); }
    catch (e) { return sendResponse(client, 500, 'Internal Server Error', 'text/plain', 'Cannot open file', clientIp, filePath); }

    if (HOT_RELOAD && mimeType === 'text/html') {
        let body = fileBuf.toString('utf8');
        const script = hotReloadScript();
        if (/<\/body>/i.test(body)) {
            body = body.replace(/<\/body>/i, script + '</body>');
        } else {
            body += script;
        }

        const bodyBuf = Buffer.from(body, 'utf8');
        const headers =
            `HTTP/1.1 ${code} ${status}\r\n` +
            `Content-Type: ${mimeType}\r\n` +
            `Content-Length: ${bodyBuf.length}\r\n` +
            'Cache-Control: no-store\r\n' +
            SECURITY_HEADERS +
            'Connection: close\r\n\r\n';

        logPacket({
            type: 'HEADERS', client_ip: clientIp, file_path: filePath,
            size: Buffer.byteLength(headers), mime_type: mimeType, file_size: bodyBuf.length,
        });

        try {
            client.write(headers);
            recordTransfer(Buffer.byteLength(headers));
            client.write(bodyBuf);
            recordTransfer(bodyBuf.length);
        } catch (e) { /* client hung up mid-write */ }
        return;
    }

    const fileSize = fileBuf.length;
    const cacheControl = code === 200 ? 'public, max-age=3600' : 'no-store';

    const headers =
        `HTTP/1.1 ${code} ${status}\r\n` +
        `Content-Type: ${mimeType}\r\n` +
        `Content-Length: ${fileSize}\r\n` +
        `Cache-Control: ${cacheControl}\r\n` +
        SECURITY_HEADERS +
        'Connection: close\r\n\r\n';

    logPacket({
        type: 'HEADERS', client_ip: clientIp, file_path: filePath,
        size: Buffer.byteLength(headers), mime_type: mimeType, file_size: fileSize,
    });

    try {
        client.write(headers);
        recordTransfer(Buffer.byteLength(headers));
    } catch (e) { return; }

    let sent = 0;
    let packetNum = 1;
    for (let offset = 0; offset < fileBuf.length; offset += BUFFER_SIZE) {
        const chunk = fileBuf.subarray(offset, Math.min(offset + BUFFER_SIZE, fileBuf.length));
        try { client.write(chunk); } catch (e) { break; }
        recordTransfer(chunk.length);
        sent += chunk.length;

        logPacket({
            type: 'DATA', client_ip: clientIp, file_path: filePath,
            size: chunk.length, packet_num: packetNum++, total_size: fileSize,
            progress: Math.floor((sent / fileSize) * 100), mime_type: mimeType,
        });
    }
}

// ======================
// 403 handling
// ======================
function serve403(client, clientIp, requestedPath) {
    sendResponse(client, 403, 'Forbidden', 'text/plain', 'Access denied', clientIp, requestedPath);
}

// ======================
// 404 handling
// ======================
function serve404(client, clientIp, requestedPath) {
    const m = (requestedPath || '').match(/\.([^.\/]+)$/);
    const ext = m ? m[1] : undefined;
    const wantsHtml = ext !== undefined && /^html?$/i.test(ext);

    if (wantsHtml) {
        let real404;
        try { real404 = fs.realpathSync(PAGE_404); } catch (e) { real404 = undefined; }
        if (real404) {
            try {
                const st = fs.statSync(real404);
                fs.accessSync(real404, fs.constants.R_OK);
                if (st.isFile()) return serveStatic(client, real404, clientIp, 404, 'Not Found');
            } catch (e) { /* status page unreadable, fall through to plain 404 */ }
        }
    }

    sendResponse(client, 404, 'Not Found', 'text/plain', 'File not found', clientIp, requestedPath);
}

// ======================
// Generic responses
// ======================
function sendResponse(client, code, status, type, body, clientIp, filePath, opts) {
    opts = opts || {};

    const bodyBuf = Buffer.from(body, 'utf8');
    const headerStr =
        `HTTP/1.1 ${code} ${status}\r\n` +
        `Content-Type: ${type}\r\n` +
        `Content-Length: ${bodyBuf.length}\r\n` +
        SECURITY_HEADERS +
        'Connection: close\r\n\r\n';

    const response = Buffer.concat([Buffer.from(headerStr, 'binary'), bodyBuf]);

    if (!opts.quiet) {
        logPacket({
            type: 'FULL_RESPONSE', client_ip: clientIp, file_path: filePath,
            size: response.length, code, status,
        });
    }

    try {
        client.write(response);
        recordTransfer(response.length);
    } catch (e) { /* client hung up */ }
}

// ======================
// Packet logger
// ======================
function truncateText(text, max) {
    if (text.length <= max) return text;
    if (max < 3) max = 3;
    return text.slice(0, max - 3) + '...';
}

function logRow(content, width) {
    width = width || LOG_WIDTH;
    let pad = width - 4 - stripLen(content);
    if (pad < 0) pad = 0;
    return `${FRAME}|${RESET} ${content}${' '.repeat(pad)} ${FRAME}|${RESET}\n`;
}

function fieldRow(label, value, color, width) {
    color = color || VALUE;
    width = width || LOG_WIDTH;

    const valueMax = width - 4 - 12;
    value = truncateText(String(value), valueMax);

    return logRow(`${LABEL}${label.padEnd(12)}${RESET}${color}${value}${RESET}`, width);
}

function browserOpenedBanner(url) {
    let width = LOG_WIDTH + 20;
    if (width > TERM_COLS) width = TERM_COLS;
    const sep = '='.repeat(width);

    return `\n${FRAME}${sep}${RESET}\n` +
        fieldRow('Opening:', url, VALUE, width) +
        `${FRAME}${sep}${RESET}\n\n`;
}

function formatTimestamp(date) {
    date = date || new Date();
    const pad = n => String(n).padStart(2, '0');
    return `${date.getFullYear()}-${pad(date.getMonth() + 1)}-${pad(date.getDate())} `
         + `${pad(date.getHours())}:${pad(date.getMinutes())}:${pad(date.getSeconds())}`;
}

function logPacket(params) {
    const now = Math.floor(Date.now() / 1000);
    if (now - lastTime >= 5) {
        startStreamBanner(`STREAM ID: #${streamCounter}`);
        streamCounter++;
    }
    lastTime = now;

    const timestamp = formatTimestamp();

    let safeFilePath = params.file_path || '';
    safeFilePath = safeFilePath.replace(/\x1b/g, '');

    if (safeFilePath === REAL_WEB_ROOT) {
        safeFilePath = '/';
    } else if (safeFilePath.indexOf(ROOT_PREFIX) === 0) {
        safeFilePath = '/' + safeFilePath.slice(ROOT_PREFIX.length);
    }

    const separator = '='.repeat(LOG_WIDTH);
    const subseparator = '-'.repeat(LOG_WIDTH);

    let output = '';
    output += `\n${FRAME}${separator}${RESET}\n`;
    output += logRow(`${LABEL}PACKET DETAILS (${RESET}${VALUE}${params.type}${RESET}${LABEL}) at ${RESET}${VALUE}${timestamp}${RESET}`);
    output += `${FRAME}${subseparator}${RESET}\n`;

    output += fieldRow('Client:', params.client_ip);

    if ('file_path' in params) {
        if (REAL_PAGE_404 !== undefined && safeFilePath === REAL_PAGE_404) {
            output += fieldRow('File:', '[404 status page]', WARN);
        } else {
            output += fieldRow('File:', safeFilePath);
        }
    }

    if ('code' in params) {
        const statusColor = params.code >= 500 ? BAD : params.code >= 400 ? WARN : GOOD;
        output += fieldRow('Status:', `${params.code} ${params.status}`, statusColor);
    }

    if ('mime_type' in params) output += fieldRow('MIME Type:', params.mime_type);

    output += fieldRow('Size:', `${params.size} bytes`);

    if ('file_size' in params) output += fieldRow('File Size:', `${params.file_size} bytes`);
    if ('packet_num' in params) output += fieldRow('Packet #:', params.packet_num);
    if ('progress' in params) output += fieldRow('Progress:', `${params.progress}%`);

    output += `${FRAME}${separator}${RESET}\n\n`;

    logOutput(output);

    let tone = 'packet';
    if ('code' in params) {
        tone = params.code >= 500 ? 'error' : params.code >= 400 ? 'warn' : 'packet';
    }
    playTone(tone);
}

process.on('exit', () => {
    saveHistory();
    saveSettings();
    if (IS_TTY && tuiActive) {
        process.stdout.write('\x1b[?7h\x1b[?25h\x1b[0m\x1b[?1049l');
        if (process.stdin.isTTY) {
            try { process.stdin.setRawMode(false); } catch (e) {}
        }
    }
    try { server.close(); } catch (e) {}
});
