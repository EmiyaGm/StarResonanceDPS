// useGlobalHover.js
const { ipcRenderer } = require('electron');

/**
 * 绑定一个全局 hover 检测
 * @param {HTMLElement} element - 要监听的元素
 * @param {Function} onEnter - 进入时回调
 * @param {Function} onLeave - 离开时回调
 */
function useGlobalHover(element, onEnter, onLeave) {
  let inside = false;

  function checkHover(pos) {
    if (!element || !element.getBoundingClientRect) return;
    const rect = element.getBoundingClientRect();

    const inElement =
      pos.x >= rect.left &&
      pos.x <= rect.right &&
      pos.y >= rect.top &&
      pos.y <= rect.bottom;

    if (inElement && !inside) {
      inside = true;
      onEnter && onEnter();
    } else if (!inElement && inside) {
      inside = false;
      onLeave && onLeave();
    }
  }

  ipcRenderer.on('global-mouse-move', (_, pos) => {
    checkHover(pos);
  });

  ipcRenderer.on('global-mouse-leave-all', () => {
    if (inside) {
      inside = false;
      onLeave && onLeave();
    }
  });
}

module.exports = { useGlobalHover };
