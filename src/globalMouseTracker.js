// globalMouseTracker.js
const { screen } = require('electron');

function initGlobalMouseTracker(win) {
  let lastPos = { x: -1, y: -1 };

  setInterval(() => {
    const pos = screen.getCursorScreenPoint();
    if (pos.x === lastPos.x && pos.y === lastPos.y) return; // 鼠标没动
    lastPos = pos;

    const bounds = win.getBounds();
    const inWindow =
      pos.x >= bounds.x &&
      pos.x <= bounds.x + bounds.width &&
      pos.y >= bounds.y &&
      pos.y <= bounds.y + bounds.height;

    if (inWindow) {
      win.webContents.send('global-mouse-move', {
        x: pos.x - bounds.x,
        y: pos.y - bounds.y
      });
    } else {
      win.webContents.send('global-mouse-leave-all');
    }
  }, 16); // 约 60 FPS
}

module.exports = { initGlobalMouseTracker };
