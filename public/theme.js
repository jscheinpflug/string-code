(function () {
  var STORAGE_KEY = 'string-code-theme';

  function applyTheme(theme) {
    document.documentElement.setAttribute('data-theme', theme);
    var btn = document.querySelector('.theme-toggle');
    if (btn) btn.textContent = theme === 'light' ? '☾' : '☀';
  }

  function toggleTheme() {
    var current = document.documentElement.getAttribute('data-theme') || 'dark';
    var next = current === 'dark' ? 'light' : 'dark';
    localStorage.setItem(STORAGE_KEY, next);
    applyTheme(next);
  }

  // Default to dark; only override if user has explicitly toggled.
  var saved = localStorage.getItem(STORAGE_KEY) || 'dark';
  applyTheme(saved);

  // Expose toggle for the onclick handler in the nav button.
  window.toggleTheme = toggleTheme;
})();
