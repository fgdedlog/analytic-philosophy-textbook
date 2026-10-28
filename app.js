/* app.js — shared behaviour: theme, menu, progress tracking, quizzes, glossary filter, search. */
(function () {
  'use strict';
  /* In the single-file edition this file is run again after every page change; FIRST guards the one-off, document-level setup. */
  var FIRST = !window.__aptInit; window.__aptInit = true;
  var LS = function () { return window.APT_LS || window.localStorage; };
  var KEY = 'apt-progress', TOTAL = 16;
  function $(s, r) { return (r || document).querySelector(s); }
  function $$(s, r) { return Array.prototype.slice.call((r || document).querySelectorAll(s)); }
  function store(k, v) { try { if (v === undefined) return LS().getItem(k); LS().setItem(k, v); } catch (e) { return null; } }

  /* Theme */
  var tbtn = $('.theme-btn');
  function setThemeLabel() {
    var dark = document.documentElement.getAttribute('data-theme') === 'dark';
    if (tbtn) tbtn.setAttribute('aria-label', dark ? 'Switch to light mode' : 'Switch to dark mode');
  }
  if (tbtn && FIRST) tbtn.addEventListener('click', function () {
    var t = document.documentElement.getAttribute('data-theme') === 'dark' ? 'light' : 'dark';
    document.documentElement.setAttribute('data-theme', t); store('apt-theme', t); setThemeLabel();
  });
  setThemeLabel();

  /* Mobile menu */
  var mbtn = $('.menu-btn'), side = $('#sidebar');
  if (mbtn && side && FIRST) {
    mbtn.addEventListener('click', function () {
      var open = side.classList.toggle('open');
      mbtn.setAttribute('aria-expanded', open ? 'true' : 'false');
      mbtn.setAttribute('aria-label', open ? 'Hide contents' : 'Show contents');
    });
    document.addEventListener('keydown', function (e) { if (e.key === 'Escape' && side.classList.contains('open')) { side.classList.remove('open'); mbtn.setAttribute('aria-expanded', 'false'); mbtn.focus(); } });
    document.addEventListener('click', function (e) { if (side.classList.contains('open') && !side.contains(e.target) && !mbtn.contains(e.target)) { side.classList.remove('open'); mbtn.setAttribute('aria-expanded', 'false'); } });
  }

  /* Progress */
  function getProg() { try { return JSON.parse(store(KEY) || '{}') || {}; } catch (e) { return {}; } }
  function setProg(p) { store(KEY, JSON.stringify(p)); renderProg(); }
  function renderProg() {
    var p = getProg(), n = 0;
    for (var k in p) if (p[k] && /^ch\d\d$/.test(k)) n++;
    $$('.toc a[data-ch]').forEach(function (a) { a.classList.toggle('done', !!p[a.getAttribute('data-ch')]); });
    var pt = $('#prog-text'); if (pt) pt.textContent = 'Progress: ' + n + ' of ' + TOTAL + ' chapters';
    var pb = $('#prog-bar'); if (pb) pb.style.width = (100 * n / TOTAL) + '%';
    var big = $('#prog-big-text'); if (big) big.textContent = n + ' of ' + TOTAL + ' chapters marked complete';
    var bb = $('#prog-big-bar'); if (bb) bb.style.width = (100 * n / TOTAL) + '%';
    $$('.part-list [data-status]').forEach(function (s) { s.textContent = p[s.getAttribute('data-status')] ? '✓ complete' : ''; });
    $$('.complete-btn').forEach(function (b) {
      var c = b.getAttribute('data-ch'), done = !!p[c], num = parseInt(c.slice(2), 10);
      b.setAttribute('aria-pressed', done ? 'true' : 'false');
      b.textContent = done ? '✓ Chapter ' + num + ' complete (click to undo)' : 'Mark chapter ' + num + ' as complete';
    });
  }
  $$('.complete-btn').forEach(function (b) {
    b.addEventListener('click', function () { var p = getProg(), c = b.getAttribute('data-ch'); if (p[c]) delete p[c]; else p[c] = Date.now(); setProg(p); });
  });
  var reset = $('#prog-reset');
  if (reset) reset.addEventListener('click', function () { if (window.confirm('Clear all progress marks?')) setProg({}); });
  renderProg();

  /* Quizzes: multiple choice */
  $$('.quiz.mc').forEach(function (q) {
    var ans = +q.getAttribute('data-answer'), fb = $('.quiz-fb', q), ex = $('.quiz-ex', q);
    $$('.opt', q).forEach(function (b) {
      b.addEventListener('click', function () {
        var k = +b.getAttribute('data-k');
        $$('.opt', q).forEach(function (o) { o.classList.remove('wrong'); });
        if (k === ans) {
          b.classList.add('right'); fb.textContent = 'Correct.'; fb.className = 'quiz-fb ok';
          if (ex && ex.textContent.trim()) ex.hidden = false;
        } else { b.classList.add('wrong'); fb.textContent = 'Not quite — try again.'; fb.className = 'quiz-fb no'; }
      });
    });
  });
  /* Quizzes: translation checked by truth table */
  $$('.quiz.tr').forEach(function (q) {
    var ref = q.getAttribute('data-answer'), inp = $('.tr-in', q), fb = $('.quiz-fb', q), ex = $('.quiz-ex', q);
    function check() {
      var L = window.Logic; if (!L) return;
      var s = inp.value.trim();
      if (!s) { fb.textContent = 'Type a formula first.'; fb.className = 'quiz-fb no'; return; }
      try {
        var mine = L.parse(s), key = L.parse(ref);
        var refAtoms = L.atoms(key), extra = L.atoms(mine).filter(function (a) { return refAtoms.indexOf(a) < 0; });
        var c = L.compare(mine, key);
        if (c.equivalent) {
          fb.textContent = 'Correct: ' + L.show(mine) + ' is logically equivalent to the model answer.' + (extra.length ? ' (It mentions ' + extra.join(', ') + ', which plays no role.)' : '');
          fb.className = 'quiz-fb ok'; ex.hidden = false;
        } else {
          var row = (c.aNotB[0] || c.bNotA[0]), parts = [];
          for (var a in row.v) parts.push(a + ' = ' + (row.v[a] ? 'T' : 'F'));
          var msg = 'Not equivalent. ' + (extra.length ? 'Note: the key does not use ' + extra.join(', ') + '. ' : '') + 'They come apart when ' + parts.join(', ') + ': your formula is ' + (row.a ? 'true' : 'false') + ' but the intended sentence is ' + (row.b ? 'true' : 'false') + '.';
          fb.textContent = msg; fb.className = 'quiz-fb no';
        }
      } catch (e) { fb.textContent = 'Could not read your formula: ' + e.message; fb.className = 'quiz-fb no'; }
    }
    $('.tr-check', q).addEventListener('click', check);
    inp.addEventListener('keydown', function (e) { if (e.key === 'Enter') check(); });
    $('.tr-show', q).addEventListener('click', function () { ex.hidden = false; });
  });

  /* Glossary filter */
  var gq = $('#gloss-q');
  if (gq) {
    var items = $$('.gloss-item'), cnt = $('#gloss-count');
    var run = function () {
      var v = gq.value.trim().toLowerCase(), shown = 0;
      items.forEach(function (it) { var ok = !v || it.getAttribute('data-text').indexOf(v) >= 0; it.hidden = !ok; if (ok) shown++; });
      $$('.gloss-sec').forEach(function (s) { s.hidden = !$$('.gloss-item', s).some(function (i) { return !i.hidden; }); });
      cnt.textContent = v ? shown + ' matching term' + (shown === 1 ? '' : 's') : items.length + ' terms';
    };
    gq.addEventListener('input', run); run();
  }

  /* Search page */
  var sres = $('#search-results');
  if (sres && window.SEARCH_INDEX) {
    var sq = $('#search-q');
    var params = new URLSearchParams(window.APT_QS ? window.APT_QS() : location.search); sq.value = params.get('q') || '';
    var top = $('#top-q'); if (top) top.value = sq.value;
    var escH = function (s) { return s.replace(/[&<>"]/g, function (c) { return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]; }); };
    var doSearch = function () {
      var q = sq.value.trim().toLowerCase(), terms = q.split(/\s+/).filter(function (t) { return t.length > 1 || /[¬∧∨→↔∀∃]/.test(t); });
      var info = $('#search-info');
      if (!terms.length) { sres.innerHTML = ''; info.textContent = 'Type at least two letters.'; return; }
      var hits = [];
      window.SEARCH_INDEX.forEach(function (e) {
        var x = e.x.toLowerCase(), h = (e.h + ' ' + e.p).toLowerCase(), score = 0;
        for (var i = 0; i < terms.length; i++) {
          var t = terms[i], c = x.split(t).length - 1, hh = h.indexOf(t) >= 0;
          if (!c && !hh) return;
          score += Math.min(c, 10) + (hh ? 15 : 0);
        }
        if (x.indexOf(q) >= 0) score += 10;
        hits.push({ e: e, s: score });
      });
      hits.sort(function (a, b) { return b.s - a.s; });
      info.textContent = hits.length + ' section' + (hits.length === 1 ? '' : 's') + ' found for “' + sq.value.trim() + '”.';
      var re = new RegExp('(' + terms.map(function (t) { return t.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'); }).join('|') + ')', 'gi');
      sres.innerHTML = hits.slice(0, 60).map(function (h) {
        var x = h.e.x, i = x.toLowerCase().indexOf(terms[0]), st = Math.max(0, i - 90);
        var snip = (st ? '… ' : '') + x.slice(st, st + 260) + '…';
        return '<li><a class="sr-t" href="' + h.e.u + '">' + escH(h.e.h || h.e.p) + '</a><div class="sr-p">' + escH(h.e.p) + '</div><p class="sr-x">' + escH(snip).replace(re, '<mark>$1</mark>') + '</p></li>';
      }).join('');
    };
    $('#search-form').addEventListener('submit', function (e) { e.preventDefault(); if (window.APT_SETQ) window.APT_SETQ('q=' + encodeURIComponent(sq.value)); else history.replaceState(null, '', '?q=' + encodeURIComponent(sq.value)); doSearch(); });
    sq.addEventListener('input', doSearch);
    doSearch();
  }

  /* Before printing, open solutions only if the reader asked for them */
  if (FIRST) window.addEventListener('beforeprint', function () {
    var want = document.body.classList.contains('print-solutions');
    $$('details.solution').forEach(function (d) { if (want) { d.setAttribute('data-was', d.open ? '1' : '0'); d.open = true; } });
  });
  if (FIRST) window.addEventListener('afterprint', function () { $$('details.solution[data-was]').forEach(function (d) { d.open = d.getAttribute('data-was') === '1'; d.removeAttribute('data-was'); }); });
  var ps = $('#print-solutions');
  if (ps) ps.addEventListener('change', function () { document.body.classList.toggle('print-solutions', ps.checked); });
})();
