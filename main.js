const { app, BrowserWindow, ipcMain, dialog } = require('electron');
const path = require('path');
const cap = require('cap');
const winston = require("winston");
const zlib = require('zlib');
const pb = require('./algo/pb');
const PacketProcessor = require('./algo/packet');
const { Readable } = require("stream");

const Cap = cap.Cap;
const decoders = cap.decoders;
const PROTOCOL = decoders.PROTOCOL;

let c;

// 全局变量
let mainWindow;
let logWindow;
let overlayWindow;
let devices = [];
let isCapturing = false;
let selectedDevice = null;
let overlayEnabled = false;


// 网络包处理变量
let user_uid;
let current_server = '';
let _data = Buffer.alloc(0);
let tcp_next_seq = -1;
let tcp_cache = {};
let tcp_cache_size = 0;
let tcp_last_time = 0;

// 日志缓存队列，用于在mainWindow创建前缓存日志
let logQueue = [];

// 内存优化变量
let dataCleanupInterval;
let statsUpdateInterval;

// 通用统计类，用于处理伤害或治疗数据
class StatisticData {
    constructor() {
        this.stats = {
            normal: 0,
            critical: 0,
            lucky: 0,
            crit_lucky: 0,
            hpLessen: 0, // 仅用于伤害统计
            total: 0,
        };
        this.count = {
            normal: 0,
            critical: 0,
            lucky: 0,
            total: 0,
        };
        this.realtimeWindow = []; // 实时统计窗口
        this.timeRange = []; // 时间范围 [开始时间, 最后时间]
        this.realtimeStats = {
            value: 0,
            max: 0,
        };
    }

    /** 添加数据记录
     * @param {number} value - 数值
     * @param {boolean} isCrit - 是否为暴击
     * @param {boolean} isLucky - 是否为幸运
     * @param {number} hpLessenValue - 生命值减少量（仅伤害使用）
     */
    addRecord(value, isCrit, isLucky, hpLessenValue = 0) {
        const now = Date.now();

        // 更新数值统计
        if (isCrit) {
            if (isLucky) {
                this.stats.crit_lucky += value;
            } else {
                this.stats.critical += value;
            }
        } else if (isLucky) {
            this.stats.lucky += value;
        } else {
            this.stats.normal += value;
        }
        this.stats.total += value;
        this.stats.hpLessen += hpLessenValue;

        // 更新次数统计
        if (isCrit) {
            this.count.critical++;
        }
        if (isLucky) {
            this.count.lucky++;
        }
        if (!isCrit && !isLucky) {
            this.count.normal++;
        }
        this.count.total++;

        this.realtimeWindow.push({
            time: now,
            value,
        });

        if (this.timeRange[0]) {
            this.timeRange[1] = now;
        } else {
            this.timeRange[0] = now;
        }
    }

    /** 更新实时统计 */
    updateRealtimeStats() {
        const now = Date.now();

        // 清除超过1秒的数据
        while (this.realtimeWindow.length > 0 && now - this.realtimeWindow[0].time > 1000) {
            this.realtimeWindow.shift();
        }

        // 计算当前实时值
        this.realtimeStats.value = 0;
        for (const entry of this.realtimeWindow) {
            this.realtimeStats.value += entry.value;
        }

        // 更新最大值
        if (this.realtimeStats.value > this.realtimeStats.max) {
            this.realtimeStats.max = this.realtimeStats.value;
        }
    }

    /** 计算总的每秒统计值 */
    getTotalPerSecond() {
        if (!this.timeRange[0] || !this.timeRange[1]) {
            return 0;
        }
        const totalPerSecond = (this.stats.total / (this.timeRange[1] - this.timeRange[0]) * 1000) || 0;
        if (!Number.isFinite(totalPerSecond)) return 0;
        return totalPerSecond;
    }

    /** 重置数据 */
    reset() {
        this.stats = {
            normal: 0,
            critical: 0,
            lucky: 0,
            crit_lucky: 0,
            hpLessen: 0,
            total: 0,
        };
        this.count = {
            normal: 0,
            critical: 0,
            lucky: 0,
            total: 0,
        };
        this.realtimeWindow = [];
        this.timeRange = [];
        this.realtimeStats = {
            value: 0,
            max: 0,
        };
    }
}

class UserData {
    constructor(uid) {
        this.uid = uid;
        this.name = '';
        this.damageStats = new StatisticData();
        this.healingStats = new StatisticData();
        this.takenDamage = 0; // 承伤
        this.profession = '未知';
        this.skillUsage = new Map(); // 技能使用情况
        this.fightPoint = 0; // 总评分
    }

    /** 添加伤害记录
     * @param {number} skillId - 技能ID/Buff ID
     * @param {number} damage - 伤害值
     * @param {boolean} isCrit - 是否为暴击
     * @param {boolean} [isLucky] - 是否为幸运
     * @param {number} hpLessenValue - 生命值减少量
     */
    addDamage(skillId, damage, isCrit, isLucky, hpLessenValue = 0) {
        this.damageStats.addRecord(damage, isCrit, isLucky, hpLessenValue);
        // 记录技能使用情况
        if (!this.skillUsage.has(skillId)) {
            this.skillUsage.set(skillId, new StatisticData());
        }
        this.skillUsage.get(skillId).addRecord(damage, isCrit, isLucky, hpLessenValue);
        this.skillUsage.get(skillId).realtimeWindow.length = 0;
    }

    /** 添加治疗记录
     * @param {number} healing - 治疗值
     * @param {boolean} isCrit - 是否为暴击
     * @param {boolean} [isLucky] - 是否为幸运
     */
    addHealing(healing, isCrit, isLucky) {
        this.healingStats.addRecord(healing, isCrit, isLucky);
    }

    /** 添加承伤记录
     * @param {number} damage - 承受的伤害值
     * */
    addTakenDamage(damage) {
        this.takenDamage += damage;
    }

    /** 设置职业
     * @param {string} profession - 职业名称
     * */
    setProfession(profession) {
        this.profession = profession;
    }

    /** 更新实时DPS和HPS 计算过去1秒内的总伤害和治疗 */
    updateRealtimeDps() {
        this.damageStats.updateRealtimeStats();
        this.healingStats.updateRealtimeStats();
    }

    /** 计算总DPS */
    getTotalDps() {
        return this.damageStats.getTotalPerSecond();
    }

    /** 计算总HPS */
    getTotalHps() {
        return this.healingStats.getTotalPerSecond();
    }

    /** 获取合并的次数统计 */
    getTotalCount() {
        return {
            normal: this.damageStats.count.normal + this.healingStats.count.normal,
            critical: this.damageStats.count.critical + this.healingStats.count.critical,
            lucky: this.damageStats.count.lucky + this.healingStats.count.lucky,
            total: this.damageStats.count.total + this.healingStats.count.total,
        };
    }

    /** 获取用户数据摘要 */
    getSummary() {
        return {
            realtime_dps: this.damageStats.realtimeStats.value,
            realtime_dps_max: this.damageStats.realtimeStats.max,
            total_dps: this.getTotalDps(),
            total_damage: { ...this.damageStats.stats },
            total_count: this.getTotalCount(),
            realtime_hps: this.healingStats.realtimeStats.value,
            realtime_hps_max: this.healingStats.realtimeStats.max,
            total_hps: this.getTotalHps(),
            total_healing: { ...this.healingStats.stats },
            taken_damage: this.takenDamage,
            profession: this.profession,
            name: this.name,
            fightPoint: this.fightPoint,
        };
    }

    /** 设置姓名
     * @param {string} name - 姓名
     * */
    setName(name) {
        this.name = name;
    }

    /** 设置用户总评分
     * @param {number} fightPoint - 总评分
     */
    setFightPoint(fightPoint) {
        this.fightPoint = fightPoint;
    }

    /** 重置数据 预留 */
    reset() {
        this.damageStats.reset();
        this.healingStats.reset();
        this.takenDamage = 0;
        this.profession = '未知';
        this.skillUsage.clear();
        this.fightPoint = 0;
    }
}

// 用户数据管理器
class UserDataManager {
    constructor() {
        this.users = new Map();
    }

    /** 获取或创建用户记录
     * @param {number} uid - 用户ID
     * @returns {UserData} - 用户数据实例
     */
    getUser(uid) {
        if (!this.users.has(uid)) {
            this.users.set(uid, new UserData(uid));
        }
        return this.users.get(uid);
    }

    /** 添加伤害记录
     * @param {number} uid - 造成伤害的用户ID
     * @param {number} skillId - 技能ID/Buff ID
     * @param {number} damage - 伤害值
     * @param {boolean} isCrit - 是否为暴击
     * @param {boolean} [isLucky] - 是否为幸运
     * @param {number} hpLessenValue - 生命值减少量
     */
    addDamage(uid, skillId, damage, isCrit, isLucky, hpLessenValue = 0) {
        const user = this.getUser(uid);
        user.addDamage(skillId, damage, isCrit, isLucky, hpLessenValue);
    }

    /** 添加治疗记录
     * @param {number} uid - 进行治疗的用户ID
     * @param {number} healing - 治疗值
     * @param {boolean} isCrit - 是否为暴击
     * @param {boolean} [isLucky] - 是否为幸运
     */
    addHealing(uid, healing, isCrit, isLucky) {
        const user = this.getUser(uid);
        user.addHealing(healing, isCrit, isLucky);
    }

    /** 添加承伤记录
     * @param {number} uid - 承受伤害的用户ID
     * @param {number} damage - 承受的伤害值
     * */
    addTakenDamage(uid, damage) {
        const user = this.getUser(uid);
        user.addTakenDamage(damage);
    }

    /** 设置用户职业
     * @param {number} uid - 用户ID
     * @param {string} profession - 职业名称
     * */
    setProfession(uid, profession) {
        const user = this.getUser(uid);
        user.setProfession(profession);
    }

    /** 设置用户姓名
     * @param {number} uid - 用户ID
     * @param {string} name - 姓名
     * */
    setName(uid, name) {
        const user = this.getUser(uid);
        user.setName(name);
    }

    /** 设置用户总评分
     * @param {number} uid - 用户ID
     * @param {number} fightPoint - 总评分
     */
    setFightPoint(uid, fightPoint) {
        const user = this.getUser(uid);
        user.setFightPoint(fightPoint);
    }

    /** 更新所有用户的实时DPS和HPS */
    updateAllRealtimeDps() {
        for (const user of this.users.values()) {
            user.updateRealtimeDps();
        }
    }

    /** 获取所有用户数据 */
    getAllUsersData() {
        const result = {};
        for (const [uid, user] of this.users.entries()) {
            result[uid] = user.getSummary();
        }
        return result;
    }

    /** 清除所有用户数据 */
    clearAll() {
        this.users.clear();
    }

    /** 获取用户列表 */
    getUserIds() {
        return Array.from(this.users.keys());
    }
}

const userDataManager = new UserDataManager();

// 自定义传输器，将日志发送到渲染进程
class ElectronTransport extends winston.transports.Console {
    log(info, callback) {
        // 先调用父类方法处理控制台输出
        super.log(info, () => {
            // 父类回调完成后，处理发送到渲染进程的逻辑
            const level = info.level.replace(/\x1b\[[0-9;]*m/g, ''); // 移除颜色码
            const logEntry = { level, message: info.message };

            // 发送到日志窗口（优先）
            if (logWindow && logWindow.webContents) {
                logWindow.webContents.send('log-message', level, info.message);
            } else {
                // 如果日志窗口没有打开，缓存日志（限制缓存大小）
                logQueue.push(logEntry);
                if (logQueue.length > 100) {
                    logQueue.shift(); // 移除最旧的日志
                }
            }

            // 只调用一次callback
            callback();
        });
    }
}

// 发送缓存的日志到渲染进程
function flushLogQueue() {
    if (mainWindow && mainWindow.webContents && logQueue.length > 0) {
        logQueue.forEach(log => {
            mainWindow.webContents.send('log-message', log.level, log.message);
        });
        logQueue = [];
    }
}

// 日志配置
const logger = winston.createLogger({
    level: 'info',
    format: winston.format.combine(
        winston.format.colorize({ all: true }),
        winston.format.timestamp({ format: 'YYYY-MM-DD HH:mm:ss' }),
        winston.format.printf(info => {
            return `[${info.timestamp}] [${info.level}] ${info.message}`;
        })
    ),
    transports: [
        new ElectronTransport()
    ]
});

// Lock类用于TCP包处理同步
class Lock {
    constructor() {
        this.queue = [];
        this.locked = false;
    }

    async acquire() {
        if (this.locked) {
            return new Promise((resolve) => this.queue.push(resolve));
        }
        this.locked = true;
    }

    release() {
        if (this.queue.length > 0) {
            const nextResolve = this.queue.shift();
            nextResolve();
        } else {
            this.locked = false;
        }
    }
}

const tcp_lock = new Lock();

// 创建主窗口
function createWindow() {
    mainWindow = new BrowserWindow({
        width: 1200,
        height: 800,
        frame: false, // 去掉标题栏
        webPreferences: {
            nodeIntegration: true,
            contextIsolation: false
        },
        icon: path.join(__dirname, 'assets/icon.png'), // 如果有图标的话
        title: '星痕共鸣 DPS 统计工具',
        titleBarStyle: 'hidden', // 隐藏标题栏
        trafficLightPosition: { x: 15, y: 15 } // macOS 窗口控制按钮位置
    });

    mainWindow.loadFile('src/index.html');

    // 页面加载完成后发送缓存的日志
    mainWindow.webContents.once('did-finish-load', () => {
        setTimeout(() => {
            flushLogQueue();
        }, 500); // 等待一段时间确保渲染进程已准备好
    });

    // 开发时打开开发者工具
    if (process.env.NODE_ENV === 'development') {
        mainWindow.webContents.openDevTools();
    }

    mainWindow.on('closed', () => {
        mainWindow = null;
        if (isCapturing) {
            stopCapture();
        }
        // 停止定时器
        stopDataUpdateTimers();
        // 关闭其他窗口
        if (logWindow) {
            logWindow.close();
        }
        if (overlayWindow) {
            overlayWindow.close();
        }
    });
}

// 创建日志窗口
function createLogWindow() {
    if (logWindow) {
        logWindow.focus();
        return;
    }

    logWindow = new BrowserWindow({
        width: 800,
        height: 600,
        frame: false,
        webPreferences: {
            nodeIntegration: true,
            contextIsolation: false
        },
        icon: path.join(__dirname, 'assets/icon.png'),
        title: '实时日志 - 星痕共鸣 DPS'
    });

    logWindow.loadFile('src/log-window.html');

    // 开发时打开开发者工具
    if (process.env.NODE_ENV === 'development') {
        logWindow.webContents.openDevTools();
    }

    logWindow.on('closed', () => {
        logWindow = null;
    });

    // 发送缓存的日志到日志窗口
    logWindow.webContents.once('did-finish-load', () => {
        setTimeout(() => {
            if (logWindow && logQueue.length > 0) {
                logQueue.forEach(log => {
                    logWindow.webContents.send('log-message', log.level, log.message);
                });
            }
        }, 500);
    });
}

// 创建悬浮窗
function createOverlayWindow() {
    if (overlayWindow) {
        overlayWindow.focus();
        return;
    }

    overlayWindow = new BrowserWindow({
        width: 320,
        height: 400,
        frame: false,
        transparent: true,
        alwaysOnTop: true,
        resizable: false,
        skipTaskbar: true,
        webPreferences: {
            nodeIntegration: true,
            contextIsolation: false
        },
        title: 'DPS悬浮窗'
    });

    overlayWindow.loadFile('src/overlay-window.html');

    // 设置初始位置到屏幕右上角
    const { screen } = require('electron');
    const primaryDisplay = screen.getPrimaryDisplay();
    const { width, height } = primaryDisplay.workAreaSize;
    overlayWindow.setPosition(width - 350, 50);
    overlayWindow.setAlwaysOnTop(true, "screen-saver")
    overlayWindow.setVisibleOnAllWorkspaces(true)

    // 开发时打开开发者工具
    if (process.env.NODE_ENV === 'development') {
        overlayWindow.webContents.openDevTools();
    }

    overlayWindow.on('closed', () => {
        overlayWindow = null;
        overlayEnabled = false;
        if (mainWindow) {
            mainWindow.webContents.send('overlay-status-changed', false);
        }
    });

    // 悬浮窗加载完成后发送初始数据
    overlayWindow.webContents.once('did-finish-load', () => {
        setTimeout(() => {
            // 发送当前玩家UID（如果有的话）
            if (user_uid && overlayWindow && overlayWindow.webContents) {
                overlayWindow.webContents.send('player-uid-updated', user_uid.toString());
                logger.info('向悬浮窗发送初始UID: ' + user_uid.toString());
            }
        }, 500);
    });

    overlayEnabled = true;
    if (mainWindow) {
        mainWindow.webContents.send('overlay-status-changed', true);
    }
}



// 获取设备列表
function getDeviceList() {
    try {
        devices = cap.deviceList();
        return devices.map((device, index) => ({
            index,
            name: device.name,
            description: device.description
        }));
    } catch (error) {
        logger.error('获取设备列表失败:', error);
        return [];
    }
}

// 清理TCP缓存
function clearTcpCache() {
    _data = Buffer.alloc(0);
    tcp_next_seq = -1;
    tcp_last_time = 0;
    tcp_cache = {};
    tcp_cache_size = 0;
}

// 开始抓包
function startCapture(deviceIndex) {
    try {
        if (isCapturing) {
            stopCapture();
        }

        const device = devices[deviceIndex];
        if (!device) {
            throw new Error('设备不存在');
        }

        selectedDevice = device;
        c = new Cap();
        const filter = 'ip and tcp';
        const bufSize = 10 * 1024 * 1024;
        const buffer = Buffer.alloc(65535);

        const linkType = c.open(device.name, filter, bufSize, buffer);
        c.setMinBytes && c.setMinBytes(0);

        logger.info(`开始在设备 ${device.description} 上抓包`);
        isCapturing = true;

        // 通知主窗口状态更新
        if (mainWindow) {
            mainWindow.webContents.send('capture-status-changed', {
                isCapturing: true,
                selectedDevice: device.description
            });
        }

        c.on('packet', async function (nbytes, trunc) {
            const buffer1 = Buffer.from(buffer);

            if (linkType === 'ETHERNET') {
                var ret = decoders.Ethernet(buffer1);

                if (ret.info.type === PROTOCOL.ETHERNET.IPV4) {
                    ret = decoders.IPV4(buffer1, ret.offset);
                    const srcaddr = ret.info.srcaddr;
                    const dstaddr = ret.info.dstaddr;

                    if (ret.info.protocol === PROTOCOL.IP.TCP) {
                        var datalen = ret.info.totallen - ret.hdrlen;
                        ret = decoders.TCP(buffer1, ret.offset);

                        const srcport = ret.info.srcport;
                        const dstport = ret.info.dstport;
                        const src_server = `${srcaddr}:${srcport} -> ${dstaddr}:${dstport}`;

                        datalen -= ret.hdrlen;
                        let buf = Buffer.from(buffer1.subarray(ret.offset, ret.offset + datalen));

                        if (tcp_last_time && Date.now() - tcp_last_time > 30000) {
                            logger.warn('无法捕获下一个包! 游戏是否关闭或断线? seq: ' + tcp_next_seq);
                            current_server = '';
                            clearTcpCache();
                        }

                        if (current_server !== src_server) {
                            try {
                                // 尝试通过小包识别服务器
                                if (buf[4] == 0) {
                                    const data = buf.subarray(10);
                                    if (data.length) {
                                        const stream = Readable.from(data, { objectMode: false });
                                        let data1;

                                        do {
                                            const len_buf = stream.read(4);
                                            if (!len_buf) break;
                                            data1 = stream.read(len_buf.readUInt32BE() - 4);

                                            const signature = Buffer.from([0x00, 0x63, 0x33, 0x53, 0x42, 0x00]);
                                            if (Buffer.compare(data1.subarray(5, 5 + signature.length), signature)) break;

                                            try {
                                                let body = pb.decode(data1.subarray(18)) || {};
                                                if (current_server !== src_server) {
                                                    current_server = src_server;
                                                    clearTcpCache();
                                                    logger.info('获取到场景服务器地址: ' + src_server);
                                                }

                                                if (data1[17] === 0x2e) {
                                                    body = body[1];
                                                    if (body[5]) {
                                                        if (!user_uid) {
                                                            user_uid = BigInt(body[5]) >> 16n;
                                                            logger.info('获取到玩家UID: ' + user_uid);
                                                        }
                                                    }
                                                }
                                            } catch (e) {
                                                // 忽略解析错误
                                            }
                                        } while (data1 && data1.length);
                                    }
                                }
                            } catch (e) {
                                // 忽略识别错误
                            }
                            return;
                        }

                        // TCP包重组处理
                        await tcp_lock.acquire();

                        if (tcp_next_seq === -1 && buf.length > 4 && buf.readUInt32BE() < 999999) { // 第一次抓包可能抓到后半段的，先丢了
                            tcp_next_seq = ret.info.seqno;
                        }

                        // logger.debug('TCP next seq: ' + tcp_next_seq);
                        tcp_cache[ret.info.seqno] = buf;
                        tcp_cache_size++;

                        while (tcp_cache[tcp_next_seq]) {
                            const seq = tcp_next_seq;
                            _data = _data.length === 0 ? tcp_cache[seq] : Buffer.concat([_data, tcp_cache[seq]]);
                            tcp_next_seq = (seq + tcp_cache[seq].length) >>> 0;
                            tcp_cache[seq] = undefined;
                            tcp_cache_size--;
                            tcp_last_time = Date.now();

                            setTimeout(() => {
                                if (tcp_cache[seq]) {
                                    tcp_cache[seq] = undefined;
                                    tcp_cache_size--;
                                }
                            }, 10000);
                        }

                        while (_data.length > 4) {
                            let packetSize = _data.readUInt32BE();

                            if (_data.length < packetSize) break;

                            if (_data.length >= packetSize) {
                                const packet = _data.subarray(0, packetSize);
                                _data = _data.subarray(packetSize);
                                const processor = new PacketProcessor({ logger, userDataManager });
                                processor.processPacket(packet);
                            } else if (packetSize > 999999) {
                                logger.error(`无效长度!! ${_data.length},${len},${_data.toString('hex')},${tcp_next_seq}`);
                                process.exit(1);
                                break;
                            }
                        }

                        tcp_lock.release();
                    }
                }
            }
        });

        return true;
    } catch (error) {
        logger.error('开始抓包失败:', error);
        isCapturing = false;
        return false;
    }
}

// 停止抓包
function stopCapture() {
    isCapturing = false;
    clearTcpCache();
    current_server = '';
    if (c) {
        c.close()
    }
    logger.info('已停止抓包');

    // 通知主窗口状态更新
    if (mainWindow) {
        mainWindow.webContents.send('capture-status-changed', {
            isCapturing: false,
            selectedDevice: null
        });
    }
}

// 清除统计数据
function clearStats() {
    userDataManager.clearAll();
    logger.info('统计数据已清除');
}

// 启动数据更新和清理定时器
function startDataUpdateTimers() {
    // 计算实时DPS
    statsUpdateInterval = setInterval(() => {
        // 发送数据到渲染进程
        // const userData = {};
        // for (const uid of Object.keys(total_damage)) {
        //     if (!userData[uid]) {
        //         userData[uid] = {
        //             realtime_dps: 0,
        //             realtime_dps_max: 0,
        //             total_dps: 0,
        //             total_damage: {
        //                 normal: 0,
        //                 critical: 0,
        //                 lucky: 0,
        //                 crit_lucky: 0,
        //                 hpLessen: 0,
        //                 total: 0,
        //                 skill: 0
        //             },
        //             total_count: {
        //                 normal: 0,
        //                 critical: 0,
        //                 lucky: 0,
        //                 total: 0,
        //             },
        //         };
        //     }

        //     userData[uid].total_damage = total_damage[uid];
        //     userData[uid].total_count = total_count[uid];
        //     userData[uid].total_dps = ((total_damage[uid].total) / (damage_time[uid][1] - damage_time[uid][0]) * 1000) || 0;
        //     userData[uid].realtime_dps = realtime_dps[uid] ? realtime_dps[uid].value : 0;
        //     userData[uid].realtime_dps_max = realtime_dps[uid] ? realtime_dps[uid].max : 0;
        // }

        // logger.info(userDataManager.getAllUsersData())

        // logger.info('old userData:' + userData)

        userDataManager.updateAllRealtimeDps();

        const newUserData = userDataManager.getAllUsersData()

        // if (Object.keys(newUserData).length > 0) {
        //     logger.info(userDataManager.getAllUsersData())
        // }

        // 发送到主窗口
        if (mainWindow && mainWindow.webContents) {
            mainWindow.webContents.send('stats-updated', newUserData);
        }

        // 发送到悬浮窗
        if (overlayWindow && overlayWindow.webContents) {
            overlayWindow.webContents.send('stats-updated', newUserData);
        }
    }, 100);

    // 内存清理定时器 - 每30秒清理一次过期数据
    dataCleanupInterval = setInterval(() => {
        const now = Date.now();
        const maxAge = 300000; // 5分钟

        // 清理过期的DPS窗口数据 TODO

        // 清理TCP缓存中的过期数据
        for (const key of Object.keys(tcp_cache)) {
            if (tcp_cache[key] && tcp_cache[key].time) {
                if (now - tcp_cache[key].time > maxAge) {
                    delete tcp_cache[key];
                    tcp_cache_size--;
                }
            }

        }

        // 限制TCP缓存大小
        if (tcp_cache_size > 1000) {
            const keys = Object.keys(tcp_cache);
            const toDelete = keys.slice(0, tcp_cache_size - 800);
            for (const key of toDelete) {
                delete tcp_cache[key];
                tcp_cache_size--;
            }
        }

        // 清理日志缓存
        if (logQueue.length > 50) {
            logQueue = logQueue.slice(-50);
        }

        logger.debug(`内存清理完成 - TCP缓存: ${tcp_cache_size}, 日志缓存: ${logQueue.length}`);
    }, 30000);
}

// 停止所有定时器
function stopDataUpdateTimers() {
    if (statsUpdateInterval) {
        clearInterval(statsUpdateInterval);
        statsUpdateInterval = null;
    }
    if (dataCleanupInterval) {
        clearInterval(dataCleanupInterval);
        dataCleanupInterval = null;
    }
}

// IPC事件处理
ipcMain.handle('get-devices', () => {
    return getDeviceList();
});

ipcMain.handle('start-capture', (event, deviceIndex) => {
    return startCapture(deviceIndex);
});

ipcMain.handle('stop-capture', () => {
    stopCapture();
    return true;
});

ipcMain.handle('clear-stats', () => {
    clearStats();
    return true;
});

ipcMain.handle('get-capture-status', () => {
    return {
        isCapturing,
        selectedDevice: selectedDevice ? selectedDevice.description : null,
        userUid: user_uid ? user_uid.toString() : null
    };
});



// 窗口控制IPC事件
ipcMain.handle('window-minimize', () => {
    if (mainWindow) {
        mainWindow.minimize();
    }
});

ipcMain.handle('window-maximize', () => {
    if (mainWindow) {
        if (mainWindow.isMaximized()) {
            mainWindow.unmaximize();
        } else {
            mainWindow.maximize();
        }
    }
});

ipcMain.handle('window-close', () => {
    if (mainWindow) {
        mainWindow.close();
    }
});

// 日志窗口控制
ipcMain.handle('show-log-window', () => {
    createLogWindow();
});

ipcMain.handle('close-log-window', () => {
    if (logWindow) {
        logWindow.close();
    }
});

// 悬浮窗控制
ipcMain.handle('toggle-overlay', () => {
    if (overlayWindow) {
        overlayWindow.close();
        return false;
    } else {
        createOverlayWindow();
        return true;
    }
});

ipcMain.handle('overlay-minimize', () => {
    if (overlayWindow) {
        overlayWindow.minimize();
    }
});

ipcMain.handle('overlay-close', () => {
    if (overlayWindow) {
        overlayWindow.close();
    }
});

ipcMain.handle('overlay-set-always-on-top', (event, alwaysOnTop) => {
    if (overlayWindow) {
        overlayWindow.setAlwaysOnTop(alwaysOnTop, "screen-saver");
        overlayWindow.setVisibleOnAllWorkspaces(alwaysOnTop)
    }
});

ipcMain.handle('get-stats-data', () => {
    userDataManager.updateAllRealtimeDps()
    const userData = userDataManager.getAllUsersData()
    // for (const uid of Object.keys(total_damage)) {
    //     if (!userData[uid]) {
    //         userData[uid] = {
    //             realtime_dps: 0,
    //             realtime_dps_max: 0,
    //             total_dps: 0,
    //             total_damage: {
    //                 normal: 0,
    //                 critical: 0,
    //                 lucky: 0,
    //                 crit_lucky: 0,
    //                 hpLessen: 0,
    //                 total: 0,
    //             },
    //             total_count: {
    //                 normal: 0,
    //                 critical: 0,
    //                 lucky: 0,
    //                 total: 0,
    //             },
    //         };
    //     }

    //     userData[uid].total_damage = total_damage[uid];
    //     userData[uid].total_count = total_count[uid];
    //     userData[uid].total_dps = ((total_damage[uid].total) / (damage_time[uid][1] - damage_time[uid][0]) * 1000) || 0;
    //     userData[uid].realtime_dps = realtime_dps[uid] ? realtime_dps[uid].value : 0;
    //     userData[uid].realtime_dps_max = realtime_dps[uid] ? realtime_dps[uid].max : 0;
    // }
    return userData;
});

ipcMain.handle('get-overlay-status', () => {
    return overlayEnabled;
});

ipcMain.handle('get-player-uid', () => {
    return user_uid ? user_uid.toString() : null;
});

// 应用事件
app.whenReady().then(() => {
    createWindow();
    startDataUpdateTimers();
});

app.on('window-all-closed', () => {
    if (process.platform !== 'darwin') {
        if (isCapturing) {
            stopCapture();
        }
        stopDataUpdateTimers();
        app.quit();
    }
});

app.on('activate', () => {
    if (BrowserWindow.getAllWindows().length === 0) {
        createWindow();
    }
});

// 错误处理
process.on('uncaughtException', (error) => {
    logger.error('未捕获的异常:', error);
});

process.on('unhandledRejection', (reason, promise) => {
    logger.error('未处理的Promise拒绝:', reason);
});