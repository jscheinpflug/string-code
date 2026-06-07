(function () {
  var path = window.location.pathname;

  function expand(section) {
    var entries = section.querySelector(':scope > .toc-entries');
    var toggle  = section.querySelector(':scope > .toc-row > .toc-toggle');
    if (entries) entries.removeAttribute('hidden');
    if (toggle)  toggle.classList.add('open');
  }

  function collapse(section) {
    var entries = section.querySelector(':scope > .toc-entries');
    var toggle  = section.querySelector(':scope > .toc-row > .toc-toggle');
    if (entries) entries.setAttribute('hidden', '');
    if (toggle)  toggle.classList.remove('open');
  }

  function init() {
    // Wire up row-click toggles (click anywhere except the title link)
    document.querySelectorAll('.toc-nav .toc-row').forEach(function (row) {
      row.addEventListener('click', function (e) {
        if (e.target.closest('a')) return;
        var section = row.parentElement;
        var entries = section.querySelector(':scope > .toc-entries');
        if (!entries) return;
        entries.hasAttribute('hidden') ? expand(section) : collapse(section);
      });
    });

    // Auto-expand every ancestor section of the current page (sidebar only).
    // Check all links: exact match for .html hrefs, prefix match for directory hrefs.
    document.querySelectorAll('#site-sidebar a[href]').forEach(function (link) {
      var href = link.getAttribute('href');
      if (!href || href === '/') return;
      var match = (path === href) || (href.endsWith('/') && path.startsWith(href));
      if (match) {
        var el = link.closest('.toc-section');
        while (el) {
          expand(el);
          var parent = el.parentElement;
          el = parent ? parent.closest('.toc-section') : null;
        }
      }
    });
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }
})();
