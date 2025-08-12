const { ipcRenderer } = require('electron');

// DOM元素引用
let statusCard, statusIndicator, currentDevice, playerUid, noDataMessage, statsContainer;
let deviceSelect, refreshDeviceBtn, startCaptureBtn, stopCaptureBtn, clearStatsBtn, showLogBtn, toggleOverlayBtn;
let totalRealtimeDps, totalMaxDps, totalAvgDps, totalDamage, statsTable, progressDamageArea, progressHealingArea;
let totalRealtimeHps, totalMaxHps, totalAvgHps, totalHealing;
let minimizeBtn, maximizeBtn, closeBtn, typeCheckBox, pinBtn;

// 全局状态
let isCapturing = false;
let statsData = {};
let overlayEnabled = false;
let isPinned = true

const ProfessionColor = {
    雷影剑士: '#A330C9',
    冰魔导师: '#69CCF0',
    涤罪恶火·战斧: '#000000',
    青岚骑士: '#C41F3B',
    森语者: '#00FF96',
    雷霆一闪·手炮: '#000000',
    巨刃守护者: '#C79C6E',
    暗灵祈舞·仪刀·仪仗: '#000000',
    神射手: '#ABD473',
    神盾骑士: '#F58CBA',
    灵魂乐手: '#33937F',
};

// 初始化函数
function initializeElements() {
    // 状态相关元素
    statusCard = document.getElementById('statusCard');
    statusIndicator = document.getElementById('statusIndicator');
    currentDevice = document.getElementById('currentDevice');
    // playerUid = document.getElementById('playerUid');

    // 主要区域
    noDataMessage = document.getElementById('noDataMessage');
    statsContainer = document.getElementById('statsContainer');

    // 控件
    deviceSelect = document.getElementById('deviceSelect');
    refreshDeviceBtn = document.getElementById('refreshDeviceBtn');
    startCaptureBtn = document.getElementById('startCaptureBtn');
    stopCaptureBtn = document.getElementById('stopCaptureBtn');
    clearStatsBtn = document.getElementById('clearStatsBtn');
    typeCheckBox = document.getElementById('typeCheckBox');
    // pinBtn = document.getElementById('pinBtn');
    // showLogBtn = document.getElementById('showLogBtn');
    // toggleOverlayBtn = document.getElementById('toggleOverlayBtn');

    // 窗口控制按钮
    minimizeBtn = document.getElementById('minimizeBtn');
    maximizeBtn = document.getElementById('maximizeBtn');
    closeBtn = document.getElementById('closeBtn');

    // 数据展示元素
    totalRealtimeDps = document.getElementById('totalRealtimeDps');
    totalMaxDps = document.getElementById('totalMaxDps');
    totalAvgDps = document.getElementById('totalAvgDps');
    totalDamage = document.getElementById('totalDamage');
    // statsTable = document.getElementById('statsTable');
    progressDamageArea = document.getElementById('progressDamageArea');
    progressHealingArea = document.getElementById('progressHealingArea');

    totalRealtimeHps = document.getElementById('totalRealtimeHps');
    totalMaxHps = document.getElementById('totalMaxHps');
    totalAvgHps = document.getElementById('totalAvgHps');
    totalHealing = document.getElementById('totalHealing');

}

// 绑定事件监听器
function bindEventListeners() {
    // 设备选择下拉框事件
    deviceSelect.addEventListener('change', () => {
        const selectedIndex = deviceSelect.value;
        if (selectedIndex !== '') {
            startCaptureBtn.disabled = false;
        } else {
            startCaptureBtn.disabled = true;
        }
    });

    // pinBtn.addEventListener('click', () => {
    //     isPinned = !isPinned;
    //     ipcRenderer.invoke('main-set-always-on-top', isPinned);
    //     updatePinButton();
    // });

    // 刷新设备按钮
    refreshDeviceBtn.addEventListener('click', async () => {
        await loadDeviceList();
    });

    // 开始抓包按钮
    startCaptureBtn.addEventListener('click', async () => {
        const selectedIndex = parseInt(deviceSelect.value);
        if (selectedIndex >= 0) {
            try {
                const success = await ipcRenderer.invoke('start-capture', selectedIndex);
                if (!success) {
                    console.error('启动抓包失败，请检查设备和权限');
                }
            } catch (error) {
                console.error('启动抓包失败:', error);
            }
        }
    });

    stopCaptureBtn.addEventListener('click', async () => {
        try {
            await ipcRenderer.invoke('stop-capture');
            // 状态更新会通过IPC事件自动处理
        } catch (error) {
            console.error('停止抓包失败:', error);
        }
    });

    clearStatsBtn.addEventListener('click', async () => {
        if (confirm('确定要清除所有统计数据吗？')) {
            try {
                await ipcRenderer.invoke('clear-stats');
                statsData = {};
                updateStatsDisplay();
            } catch (error) {
                console.error('清除统计失败:', error);
            }
        }
    });

    // 显示日志窗口
    // showLogBtn.addEventListener('click', async () => {
    //     try {
    //         await ipcRenderer.invoke('show-log-window');
    //     } catch (error) {
    //         console.error('打开日志窗口失败:', error);
    //     }
    // });

    // 切换悬浮窗
    // toggleOverlayBtn.addEventListener('click', async () => {
    //     try {
    //         const enabled = await ipcRenderer.invoke('toggle-overlay');
    //         updateOverlayButton(enabled);
    //     } catch (error) {
    //         console.error('切换悬浮窗失败:', error);
    //     }
    // });

    // 窗口控制按钮事件
    if (minimizeBtn) {
        minimizeBtn.addEventListener('click', async () => {
            await ipcRenderer.invoke('window-minimize');
        });
    }

    if (maximizeBtn) {
        maximizeBtn.addEventListener('click', async () => {
            await ipcRenderer.invoke('window-maximize');
        });
    }

    if (closeBtn) {
        closeBtn.addEventListener('click', async () => {
            if (isCapturing && !confirm('正在进行数据包捕获，确定要关闭吗？')) {
                return;
            }
            await ipcRenderer.invoke('window-close');
        });
    }
}

// IPC事件监听
function bindIpcListeners() {
    // 接收统计数据更新
    ipcRenderer.on('stats-updated', (event, data) => {
        statsData = data;
        updateStatsDisplay();
    });

    // 接收玩家UID更新
    // ipcRenderer.on('player-uid-updated', (event, uid) => {
    //     playerUid.textContent = uid || '未获取';
    // });

    // 接收抓包状态变化
    ipcRenderer.on('capture-status-changed', (event, status) => {
        updateCaptureStatus(status.isCapturing, status.selectedDevice);
    });

    // 接收悬浮窗状态变化
    ipcRenderer.on('overlay-status-changed', (event, enabled) => {
        overlayEnabled = enabled;
        updateOverlayButton(enabled);
    });
}

function updatePinButton() {
    if (pinBtn) {
        const pinIcon = pinBtn.querySelector('span');
        if (isPinned) {
            pinIcon.textContent = '📌';
            pinBtn.title = '点击取消置顶';
        } else {
            pinIcon.textContent = '📍';
            pinBtn.title = '点击置顶显示';
        }
    }
}

// 更新抓包状态
function updateCaptureStatus(capturing, deviceName = null) {
    isCapturing = capturing;

    if (capturing) {
        statusCard.className = 'status-card capturing flex items-center justify-center';
        statusIndicator.querySelector('.status-text').textContent = '正在抓包';
        startCaptureBtn.disabled = true;
        stopCaptureBtn.disabled = false;
        if (deviceSelect) deviceSelect.disabled = true;
        if (refreshDeviceBtn) refreshDeviceBtn.disabled = true;

        if (deviceName) {
            currentDevice.textContent = deviceName;
        }
    } else {
        statusCard.className = 'status-card flex items-center justify-center';
        statusIndicator.querySelector('.status-text').textContent = '待连接';
        startCaptureBtn.disabled = !deviceSelect || deviceSelect.value === '';
        stopCaptureBtn.disabled = true;
        if (deviceSelect) deviceSelect.disabled = false;
        if (refreshDeviceBtn) refreshDeviceBtn.disabled = false;

        // 如果停止抓包，重置设备显示
        if (deviceName === null) {
            currentDevice.textContent = '未选择';
        }
    }
}

// 格式化数字显示
function formatNumber(num, decimals = 0) {
    if (typeof num !== 'number' || isNaN(num)) return '0';

    if (num >= 1000000) {
        return (num / 1000000).toFixed(1) + 'M';
    } else if (num >= 1000) {
        return (num / 1000).toFixed(1) + 'K';
    } else {
        return num.toFixed(decimals);
    }
}

// 格式化百分比
function formatPercentage(num) {
    if (typeof num !== 'number' || isNaN(num)) return '0%';
    return (num * 100).toFixed(1) + '%';
}

// 更新统计数据显示
function updateStatsDisplay() {
    const userIds = Object.keys(statsData);

    if (userIds.length === 0 && !isCapturing) {
        noDataMessage.style.display = 'block';
        statsContainer.style.display = 'none';
        return;
    }

    noDataMessage.style.display = 'none';
    statsContainer.style.display = 'block';

    console.log(typeCheckBox.checked)

    if (typeCheckBox) {
        if (typeCheckBox.checked) {
            // 显示治疗区域
            progressDamageArea.style.display = 'none'
            progressHealingArea.style.display = 'block'
        } else {
            // 显示伤害区域
            progressDamageArea.style.display = 'block'
            progressHealingArea.style.display = 'none'
        }
    } else {
        progressDamageArea.style.display = 'none'
        progressHealingArea.style.display = 'none'
    }

    // 计算总体统计
    let totalRealtimeDpsValue = 0;
    let totalMaxDpsValue = 0;
    let totalAvgDpsValue = 0;
    let totalDamageValue = 0;
    let playerCount = 0;

    let totalRealtimeHpsValue = 0;
    let totalMaxHpsValue = 0;
    let totalAvgHpsValue = 0;
    let totalHealingValue = 0;

    for (const uid of userIds) {
        const userData = statsData[uid];
        totalRealtimeDpsValue += userData.realtime_dps || 0;
        totalMaxDpsValue = Math.max(totalMaxDpsValue, userData.realtime_dps_max || 0);
        totalAvgDpsValue += userData.total_dps || 0;
        totalDamageValue += userData.total_damage.total || 0;

        totalRealtimeHpsValue += userData.realtime_hps || 0;
        totalMaxHpsValue = Math.max(totalMaxHpsValue, userData.realtime_hps_max || 0);
        totalAvgHpsValue += userData.total_hps || 0;
        totalHealingValue += userData.total_healing.total || 0;

        playerCount++;
    }



    if (playerCount > 0) {
        totalAvgDpsValue = totalAvgDpsValue / playerCount;
        totalAvgHpsValue = totalAvgHpsValue / playerCount;
    }

    // 更新概览卡片
    // totalRealtimeDps.textContent = formatNumber(totalRealtimeDpsValue);
    // totalMaxDps.textContent = formatNumber(totalMaxDpsValue);
    // totalAvgDps.textContent = formatNumber(totalAvgDpsValue);
    // totalDamage.textContent = formatNumber(totalDamageValue);

    // totalRealtimeHps.textContent = formatNumber(totalRealtimeHpsValue);
    // totalMaxHps.textContent = formatNumber(totalMaxHpsValue);
    // totalAvgHps.textContent = formatNumber(totalAvgHpsValue);
    // totalHealing.textContent = formatNumber(totalHealingValue);

    // 更新表格
    // updateStatsTable();

    // 更新进度条区域
    updateProgressArea();

    // 更新图表进度条
    // updateMetricCharts();
}

// 更新进度条区域
function updateProgressArea() {
    const userIds = Object.keys(statsData).sort();
    let max_total_damage = 0
    let max_total_healing = 0
    const damageUserDatas = []
    const healingUserDatas = []
    for (const uid of userIds) {
        const userData = statsData[uid];
        const damage = userData.total_damage;
        const healing = userData.total_healing;
        max_total_damage = Math.max(max_total_damage, damage.total)
        max_total_healing = Math.max(max_total_healing, healing.total)
        if (damage.total) {
            damageUserDatas.push({
                ...userData,
                uid
            })
        }
        if (healing.total) {
            healingUserDatas.push({
                ...userData,
                uid
            })
        }
    }

    const damageAllUserData = damageUserDatas.sort((a, b) => (b.total_damage.total - a.total_damage.total))

    const healingAllUserData = healingUserDatas.sort((a, b) => (b.total_healing.total - a.total_healing.total))

    let damageDataShow = ''
    let healingDataShow = ''

    for (const userData of damageAllUserData) {
        const damage = userData.total_damage;
        const totalDamagePercentProgress = (parseFloat(damage.total || 0) / max_total_damage) * 100;
        damageDataShow += `<div class="w-full" style="margin-bottom: 5px;background: rgba(0, 0, 0, 0.4);color: white;position: relative">
            <div class="w-full flex items-center h-[20px]" style="position: absolute;top: 0;left: 0;justify-content: space-between">
                <div> ${userData.name ? `${userData.name}(${userData.uid})` : userData.uid}(${userData.profession})(GS: ${userData.fightPoint || 0})</div>
                <div>${formatNumber(damage.total)}(${formatNumber(userData.total_dps)})</div>
            </div>
            <div class="h-[20px]" style="width: ${Math.min(totalDamagePercentProgress, 100)}%;background: ${ProfessionColor[userData.profession.split('-')[0]] ? ProfessionColor[userData.profession.split('-')[0]] : '#000000'};">
               
            </div>
        </div>`
    }

    for (const userData of healingAllUserData) {
        const healing = userData.total_healing;
        const totalHealingPercentProgress = (parseFloat(healing.total || 0) / max_total_healing) * 100;
        healingDataShow += `<div class="w-full" style="margin-bottom: 5px;background: rgba(0, 0, 0, 0.4);color: white;position: relative">
            <div class="w-full flex items-center h-[20px]" style="position: absolute;top: 0;left: 0;justify-content: space-between">
                <div>${userData.name ? `${userData.name}(${userData.uid})` : userData.uid}(${userData.profession})(GS: ${userData.fightPoint || 0})</div>
                <div>${formatNumber(healing.total)}(${formatNumber(userData.total_hps)})</div>
            </div>
            <div class="h-[20px]" style="width: ${Math.min(totalHealingPercentProgress, 100)}%;background: ${ProfessionColor[userData.profession.split('-')[0]] ? ProfessionColor[userData.profession.split('-')[0]] : '#000000'};color: white;">
                
            </div>
        </div>`
    }

    if (progressDamageArea) {
        progressDamageArea.innerHTML = damageDataShow
        progressHealingArea.innerHTML = healingDataShow
        // progressArea.appendChild(dataShow)

    }

}

// 更新统计表格
function updateStatsTable() {
    const tbody = statsTable.querySelector('tbody');
    tbody.innerHTML = '';

    const userIds = Object.keys(statsData).sort();

    for (const uid of userIds) {
        const userData = statsData[uid];
        const damage = userData.total_damage;
        const healing = userData.total_healing;
        const count = userData.total_count;

        if (damage.total || healing.total) {
            // 计算暴击率
            const critRate = count.total > 0 ? count.critical / count.total : 0;

            const row = document.createElement('tr');
            row.className = 'stats-update';

            row.innerHTML = `
            <td>${userData.name ? `${userData.name}(${uid})` : uid}(${userData.profession})${playerUid.textContent == uid ? '(你)' : ''}</td>
            <td class="number">${formatNumber(userData.realtime_dps)}/${formatNumber(userData.realtime_hps)}</td>
            <td class="number">${formatNumber(userData.realtime_dps_max)}/${formatNumber(userData.realtime_hps_max)}</td>
            <td class="number">${formatNumber(userData.total_dps)}/${formatNumber(userData.total_hps)}</td>
            <td class="number">${formatNumber(damage.total)}/${formatNumber(healing.total)}</td>
            <td class="number">${formatNumber(damage.normal)}/${formatNumber(healing.normal)}</td>
            <td class="number">${formatNumber(damage.critical)}/${formatNumber(healing.normal)}</td>
            <td class="number">${formatNumber(damage.lucky)}/${formatNumber(healing.normal)}</td>
            <td class="number">${formatNumber(damage.crit_lucky)}/${formatNumber(healing.normal)}</td>
            <td class="number">${count.total}</td>
            <td class="number">${formatPercentage(critRate)}</td>
        `;

            tbody.appendChild(row);

            // 移除动画类
            setTimeout(() => {
                row.classList.remove('stats-update');
            }, 500);
        }
    }
}

// 添加日志消息
function addLogMessage(level, message) {
    const now = new Date();
    const timeString = now.toLocaleTimeString('zh-CN', {
        hour12: false,
        hour: '2-digit',
        minute: '2-digit',
        second: '2-digit'
    });

    const logItem = document.createElement('div');
    logItem.className = 'log-item';
    logItem.innerHTML = `
        <div class="log-time">${timeString}</div>
        <div class="log-message">
            <span class="log-level ${level}">${level.toUpperCase()}</span>
            ${message}
        </div>
    `;

    logContent.appendChild(logItem);
    logContent.scrollTop = logContent.scrollHeight;

    // 保存到内存中
    logMessages.push({ timestamp: timeString, level, message });

    // 更新日志计数
    updateLogCount();

    // 限制日志数量
    if (logMessages.length > 1000) {
        logMessages.shift();
        if (logContent.children.length > 1000) {
            logContent.removeChild(logContent.firstChild);
        }
    }
}

// 更新日志计数
function updateLogCount() {
    if (logCount) {
        logCount.textContent = logMessages.length;
    }
}

// 更新指标图表
function updateMetricCharts() {
    const maxValue = Math.max(
        parseFloat(totalRealtimeDps.textContent.replace(/[^\d.]/g, '') || 0),
        parseFloat(totalMaxDps.textContent.replace(/[^\d.]/g, '') || 0),
        parseFloat(totalAvgDps.textContent.replace(/[^\d.]/g, '') || 0)
    );

    const maxHealingValue = Math.max(
        parseFloat(totalRealtimeHps.textContent.replace(/[^\d.]/g, '') || 0),
        parseFloat(totalMaxHps.textContent.replace(/[^\d.]/g, '') || 0),
        parseFloat(totalAvgHps.textContent.replace(/[^\d.]/g, '') || 0)
    );

    if (maxValue > 0) {
        // 更新实时DPS进度条
        const realtimeDpsPercent = (parseFloat(totalRealtimeDps.textContent.replace(/[^\d.]/g, '') || 0) / maxValue) * 100;
        const realtimeChart = document.querySelector('.metric-card.primary .chart-bar');
        if (realtimeChart) {
            realtimeChart.style.width = `${Math.min(realtimeDpsPercent, 100)}%`;
        }

        // 更新峰值DPS进度条
        const maxDpsPercent = (parseFloat(totalMaxDps.textContent.replace(/[^\d.]/g, '') || 0) / maxValue) * 100;
        const maxChart = document.querySelector('.metric-card.danger .chart-bar');
        if (maxChart) {
            maxChart.style.width = `${Math.min(maxDpsPercent, 100)}%`;
        }

        // 更新平均DPS进度条
        const avgDpsPercent = (parseFloat(totalAvgDps.textContent.replace(/[^\d.]/g, '') || 0) / maxValue) * 100;
        const avgChart = document.querySelector('.metric-card.success .chart-bar');
        if (avgChart) {
            avgChart.style.width = `${Math.min(avgDpsPercent, 100)}%`;
        }

        // 总伤害使用独立的缩放
        const totalDamageValue = parseFloat(totalDamage.textContent.replace(/[^\d.]/g, '') || 0);
        const damageChart = document.querySelector('.metric-card.warning .chart-bar');
        if (damageChart && totalDamageValue > 0) {
            // 使用对数缩放来更好地显示大数值
            const damagePercent = Math.min((Math.log10(totalDamageValue + 1) / Math.log10(1000000)) * 100, 100);
            damageChart.style.width = `${damagePercent}%`;
        }
    }

    if (maxHealingValue > 0) {
        // 更新实时DPS进度条
        const realtimeHpsPercent = (parseFloat(totalRealtimeHps.textContent.replace(/[^\d.]/g, '') || 0) / maxHealingValue) * 100;
        const realtimeChart = document.querySelector('.metric-card.primary .chart-healing-bar');
        if (realtimeChart) {
            realtimeChart.style.width = `${Math.min(realtimeHpsPercent, 100)}%`;
        }

        // 更新峰值DPS进度条
        const maxHpsPercent = (parseFloat(totalMaxHps.textContent.replace(/[^\d.]/g, '') || 0) / maxHealingValue) * 100;
        const maxChart = document.querySelector('.metric-card.danger .chart-healing-bar');
        if (maxChart) {
            maxChart.style.width = `${Math.min(maxHpsPercent, 100)}%`;
        }

        // 更新平均DPS进度条
        const avgHpsPercent = (parseFloat(totalAvgHps.textContent.replace(/[^\d.]/g, '') || 0) / maxHealingValue) * 100;
        const avgChart = document.querySelector('.metric-card.success .chart-healing-bar');
        if (avgChart) {
            avgChart.style.width = `${Math.min(avgHpsPercent, 100)}%`;
        }

        // 总伤害使用独立的缩放
        const totalHealingValue = parseFloat(totalHealing.textContent.replace(/[^\d.]/g, '') || 0);
        const healingChart = document.querySelector('.metric-card.warning .chart-healing-bar');
        if (healingChart && totalHealingValue > 0) {
            // 使用对数缩放来更好地显示大数值
            const healingPercent = Math.min((Math.log10(totalHealingValue + 1) / Math.log10(1000000)) * 100, 100);
            healingChart.style.width = `${healingPercent}%`;
        }
    }

}

// 加载设备列表
async function loadDeviceList() {
    try {
        deviceSelect.disabled = true;
        deviceSelect.innerHTML = '<option value="">正在加载设备...</option>';

        const devices = await ipcRenderer.invoke('get-devices');

        deviceSelect.innerHTML = '<option value="">请选择网络设备</option>';

        if (devices.length === 0) {
            deviceSelect.innerHTML = '<option value="">未找到可用设备</option>';
            console.warn('未找到可用的网络设备，请检查权限或网络连接');
            return;
        }

        devices.forEach(device => {
            const option = document.createElement('option');
            option.value = device.index;
            option.textContent = device.description;
            option.title = device.name;
            deviceSelect.appendChild(option);
        });

        deviceSelect.disabled = false;
        // 确保开始按钮初始状态为禁用
        startCaptureBtn.disabled = true;
        console.info(`已加载 ${devices.length} 个网络设备`);

    } catch (error) {
        deviceSelect.innerHTML = '<option value="">加载失败</option>';
        console.error('获取设备列表失败:', error);
    }
}

// 初始化状态
async function initializeStatus() {
    try {
        const status = await ipcRenderer.invoke('get-capture-status');
        updateCaptureStatus(status.isCapturing, status.selectedDevice);

        // if (status.userUid) {
        //     playerUid.textContent = status.userUid;
        // }

        console.info('应用程序已启动');

        // 加载设备列表
        await loadDeviceList();

        // 检查悬浮窗状态
        const overlayStatus = await ipcRenderer.invoke('get-overlay-status');
        updateOverlayButton(overlayStatus);

        if (status.isCapturing) {
            console.info(`正在设备 "${status.selectedDevice}" 上抓包`);
        }
    } catch (error) {
        console.error('获取初始状态失败:', error);
    }
}

// 键盘快捷键
function bindKeyboardShortcuts() {
    document.addEventListener('keydown', (event) => {
        if (event.ctrlKey) {
            switch (event.key) {
                case 'r':
                case 'R':
                    event.preventDefault();
                    if (!isCapturing) {
                        refreshDeviceBtn.click();
                    }
                    break;
                case 's':
                case 'S':
                    event.preventDefault();
                    if (isCapturing) {
                        stopCaptureBtn.click();
                    }
                    break;
                case 'l':
                case 'L':
                    event.preventDefault();
                    clearLogBtn.click();
                    break;
                case 'd':
                case 'D':
                    event.preventDefault();
                    clearStatsBtn.click();
                    break;
            }
        }
    });
}

// 工具提示
function addTooltips() {
    const tooltips = {
        'refreshDeviceBtn': 'Ctrl+R - 刷新设备列表',
        'stopCaptureBtn': 'Ctrl+S - 停止抓包',
        'clearStatsBtn': 'Ctrl+D - 清除统计数据',
        'clearLogBtn': 'Ctrl+L - 清除日志'
    };

    for (const [id, tooltip] of Object.entries(tooltips)) {
        const element = document.getElementById(id);
        if (element) {
            element.title = tooltip;
        }
    }
}

// 主初始化函数
async function initialize() {
    initializeElements();
    bindEventListeners();
    bindIpcListeners();
    bindKeyboardShortcuts();
    updatePinButton();
    addTooltips();
    await initializeStatus();

    // 定期更新时间显示（如果需要）
    setInterval(() => {
        // 可以在这里添加定期更新的逻辑
    }, 1000);
}

// 页面加载完成后初始化
document.addEventListener('DOMContentLoaded', initialize);

// 窗口关闭前确认和内存清理
window.addEventListener('beforeunload', (event) => {
    // 清理数据引用以释放内存
    statsData = null;

    if (isCapturing) {
        event.preventDefault();
        event.returnValue = '正在进行数据包捕获，确定要关闭吗？';
        return event.returnValue;
    }
});

// 导出一些函数供调试使用
window.debugAPI = {
    getStatsData: () => statsData,
    addTestData: () => {
        // 添加测试数据用于开发调试
        const testData = {
            '1': {
                realtime_dps: 15420,
                realtime_dps_max: 23450,
                total_dps: 18500,
                total_damage: {
                    normal: 250000,
                    critical: 180000,
                    lucky: 45000,
                    crit_lucky: 32000,
                    hpLessen: 5000,
                    total: 507000
                },
                total_count: {
                    normal: 125,
                    critical: 89,
                    lucky: 23,
                    total: 237
                }
            },
            '2': {
                realtime_dps: 15420,
                realtime_dps_max: 23450,
                total_dps: 18500,
                total_damage: {
                    normal: 250000,
                    critical: 180000,
                    lucky: 45000,
                    crit_lucky: 32000,
                    hpLessen: 5000,
                    total: 507000
                },
                total_count: {
                    normal: 125,
                    critical: 89,
                    lucky: 23,
                    total: 237
                }
            },
            '3': {
                realtime_dps: 15420,
                realtime_dps_max: 23450,
                total_dps: 18500,
                total_damage: {
                    normal: 250000,
                    critical: 180000,
                    lucky: 45000,
                    crit_lucky: 32000,
                    hpLessen: 5000,
                    total: 507000
                },
                total_count: {
                    normal: 125,
                    critical: 89,
                    lucky: 23,
                    total: 237
                }
            },
            '4': {
                realtime_dps: 15420,
                realtime_dps_max: 23450,
                total_dps: 18500,
                total_damage: {
                    normal: 250000,
                    critical: 180000,
                    lucky: 45000,
                    crit_lucky: 32000,
                    hpLessen: 5000,
                    total: 507000
                },
                total_count: {
                    normal: 125,
                    critical: 89,
                    lucky: 23,
                    total: 237
                }
            }
        };
        statsData = testData;
        updateStatsDisplay();
        console.info('已添加测试数据');
    }
};

// 更新悬浮窗按钮状态
function updateOverlayButton(enabled) {
    overlayEnabled = enabled;
    if (toggleOverlayBtn) {
        const btnText = toggleOverlayBtn.querySelector('.btn-text');
        const btnIcon = toggleOverlayBtn.querySelector('.btn-icon');

        if (enabled) {
            btnText.textContent = '关闭悬浮窗';
            btnIcon.textContent = '📱';
            toggleOverlayBtn.classList.remove('btn-outline');
            toggleOverlayBtn.classList.add('btn-success');
        } else {
            btnText.textContent = '悬浮窗';
            btnIcon.textContent = '📱';
            toggleOverlayBtn.classList.remove('btn-success');
            toggleOverlayBtn.classList.add('btn-outline');
        }
    }
}