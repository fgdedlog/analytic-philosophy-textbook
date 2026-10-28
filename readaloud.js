/* readaloud.js — "Read aloud" for chapters and reference pages, using the browser's Web Speech API (speechSynthesis).
   Pure helpers (speakText, speakFormula, chunk, splitSentences) are exported for node tests; the UI part only runs in a browser.
   In the single-file edition this file is run again after every page change: init() first tears down the previous instance. */
(function (root) {
  'use strict';

  /* ---------------------------------------------------------------- symbols → speech */
  var SYMBOLS = {
    '¬': 'not', '∼': 'not', '∧': 'and', '∨': 'or', '→': 'implies', '⊃': 'implies', '⇒': 'implies', '↔': 'if and only if', '⇔': 'if and only if',
    '≡': 'is equivalent to', '⊥': 'contradiction', '⊤': 'true', '⊢': 'proves', '⊬': 'does not prove', '⊨': 'entails', '⊭': 'does not entail',
    '∴': 'therefore', '∵': 'because', '□': 'necessarily', '◇': 'possibly', '◻': 'necessarily', '◊': 'possibly',
    '∀': 'for all', '∃': 'there exists', '=': 'equals', '≠': 'is not equal to', '≤': 'is less than or equal to', '≥': 'is greater than or equal to',
    '∈': 'is a member of', '∉': 'is not a member of', '⊆': 'is a subset of', '⊂': 'is a proper subset of', '⊇': 'is a superset of',
    '⟺': 'if and only if', '⟷': 'if and only if', '⟨': 'the pair', '⟩': '', '−': 'minus', '§': 'section', '★': 'starred', '∪': 'union', '∩': 'intersection', '∅': 'the empty set', '⊕': 'exclusive or', '×': 'times', '≈': 'is approximately',
    'φ': 'phi', 'ϕ': 'phi', 'ψ': 'psi', 'χ': 'chi', 'α': 'alpha', 'β': 'beta', 'γ': 'gamma', 'δ': 'delta', 'ε': 'epsilon', 'λ': 'lambda',
    'μ': 'mu', 'σ': 'sigma', 'τ': 'tau', 'ω': 'omega', 'π': 'pi', 'ι': 'iota', 'Γ': 'Gamma', 'Δ': 'Delta', 'Σ': 'Sigma', 'Φ': 'Phi', 'Ψ': 'Psi', 'Ω': 'Omega'
  };
  var SYM_RE = new RegExp('[' + Object.keys(SYMBOLS).join('') + ']', 'g');
  var RULE_WORD = { 'I': 'introduction', 'E': 'elimination' };
  var SUBS = { 'ₙ': 'n', 'ₘ': 'm', 'ᵢ': 'i', 'ⱼ': 'j', '₀': 0, '₁': 1, '₂': 2, '₃': 3, '₄': 4, '₅': 5, '₆': 6, '₇': 7, '₈': 8, '₉': 9 };
  var NOT_PRED = /^(If|Is|It|In|On|No|So|Or|An|As|At|By|Do|Go|He|Me|My|Of|To|Up|We|All|And|Not|The|Has|Her|His|Its|Let|Now|One|Our|Say|She|Two|Who|Why|You)$/;

  function sym(c) { return ' ' + SYMBOLS[c] + ' '; }
  function tidy(s) {
    return s.replace(/[\u00a0\u2009\u202f\u200b\u00ad]/g, function (c) { return c === '\u00ad' || c === '\u200b' ? '' : ' '; })
      .replace(/\s+/g, ' ').replace(/\(\s+/g, '(').replace(/\s+\)/g, ')').replace(/\s+([,.;:!?])/g, '$1').replace(/([,;:])\1+/g, '$1').trim();
  }
  function subscripts(s) { return s.replace(/[₀-₉ₙₘᵢⱼ]+/g, function (m) { var n = ''; for (var i = 0; i < m.length; i++) n += SUBS[m[i]]; return ' ' + n + ' '; }); }
  function dashes(s) {
    return s.replace(/(\d)\s*[–—]\s*(\d)/g, '$1 to $2').replace(/\s*[—–]\s*/g, ', ');
  }

  /* Ordinary prose (symbols still converted so they are not skipped). */
  function speakText(s) {
    s = String(s == null ? '' : s);
    s = s.replace(/([¬∧∨→↔∀∃⊥=])([IE])(?![A-Za-z0-9])/g, function (m, a, b) { return sym(a) + RULE_WORD[b] + ' '; }); // rule names: ∧I, →E …
    s = s.replace(/&(?![A-Za-z#]+;)/g, ' and ');
    s = s.replace(/(^|\s)~(?=\s|$)/g, '$1 tilde ').replace(/ \+ /g, ' plus ').replace(/ < /g, ' less than ');
    s = s.replace(SYM_RE, sym);
    s = subscripts(dashes(s));
    return tidy(s);
  }

  /* A formula (inside .fm): also speaks brackets and splits predicate letters ("Fxy" → "F x y"). */
  function speakFormula(s) {
    s = String(s == null ? '' : s);
    s = s.replace(/([∀∃])(!?)\s*([a-z])([₀-₉ₙₘᵢⱼ]*)/g, function (m, q, bang, v, sub) { return ' ' + (q === '∀' ? 'for all' : (bang ? 'there exists exactly one' : 'there exists')) + ' ' + v + (sub ? subscripts(sub) : '') + ', '; });
    s = s.replace(/\b([A-Z])([a-z]{1,3})(?![A-Za-z])/g, function (m, a, b) { return NOT_PRED.test(m) ? m : a + ' ' + b.split('').join(' '); });
    s = s.replace(/[(\[]/g, ' open bracket ').replace(/[)\]]/g, ' close bracket ').replace(/\{/g, ' open brace ').replace(/\}/g, ' close brace ');
    s = s.replace(/…|\.\.\./g, ' and so on ').replace(/′/g, ' prime ').replace(/</g, ' less than ').replace(/>/g, ' greater than ');
    s = s.replace(SYM_RE, sym);
    s = subscripts(s);
    return tidy(s);
  }

  /* Typed ASCII syntax inside <code> ("p -> q", "|=", "forall x"). */
  function speakCode(s) {
    s = ' ' + String(s == null ? '' : s) + ' ';
    s = s.replace(/<->|<=>/g, ' if and only if ').replace(/->|=>/g, ' implies ').replace(/\|=/g, ' entails ').replace(/\|-/g, ' proves ')
      .replace(/_\|_/g, ' contradiction ').replace(/[~!]/g, ' not ').replace(/[&^]/g, ' and ').replace(/\|/g, ' or ').replace(/\s[vV]\s/g, ' or ').replace(/#/g, ' contradiction ');
    return speakFormula(s);
  }

  /* ---------------------------------------------------------------- chunking */
  var ABBR = /(^|[^A-Za-z])(e\.g|i\.e|cf|vs|viz|Dr|Mr|Mrs|Ms|Prof|St|No|ch|pp?|fig|ca?|al|approx|Ltd|Jr|Sr|[A-Z])$/;
  function splitSentences(text) {
    var out = [], start = 0, n = text.length;
    for (var i = 0; i < n; i++) {
      var c = text[i];
      if (c !== '.' && c !== '!' && c !== '?') continue;
      var j = i + 1;
      while (j < n && /["'”’)\]]/.test(text[j])) j++;
      if (j < n && !/\s/.test(text[j])) continue;       // "3.5", "e.g.x"
      var k = j; while (k < n && /\s/.test(text[k])) k++;
      if (k >= n) break;                                 // end of text
      if (c === '.' && ABBR.test(text.slice(start, i))) continue;
      if (!/[A-Z0-9“"‘'(\[]/.test(text[k])) continue;    // continues in lower case
      out.push(text.slice(start, j).trim()); start = k; i = k - 1;
    }
    var rest = text.slice(start).trim(); if (rest) out.push(rest);
    return out;
  }
  function splitLong(s, max) {
    var out = [];
    while (s.length > max) {
      var win = s.slice(0, max + 1), cut = -1, m, re = /[,;:]\s/g;
      while ((m = re.exec(win))) if (m.index + 1 >= max * 0.35 && m.index + 1 <= max) cut = m.index + 1;
      if (cut < 0) { cut = win.lastIndexOf(' '); if (cut < max * 0.3) cut = max; }
      out.push(s.slice(0, cut).trim()); s = s.slice(cut).trim();
    }
    if (s) out.push(s);
    return out;
  }
  /* Split spoken text into utterances of at most `max` characters (default 160, always < 200), preferring sentence ends. */
  function chunk(text, max) {
    max = max || 160;
    text = tidy(String(text == null ? '' : text));
    if (!text) return [];
    var out = [], cur = '';
    splitSentences(text).forEach(function (s) {
      (s.length <= max ? [s] : splitLong(s, max)).forEach(function (p) {
        if (cur && (cur + ' ' + p).length <= max) cur += ' ' + p;
        else { if (cur) out.push(cur); cur = p; }
      });
    });
    if (cur) out.push(cur);
    return out;
  }

  var API = { speakText: speakText, speakFormula: speakFormula, speakCode: speakCode, chunk: chunk, splitSentences: splitSentences };
  if (typeof module === 'object' && module.exports) module.exports = API;
  if (typeof document === 'undefined' || !root || !root.document) return;

  /* ---------------------------------------------------------------- page → blocks */
  var BLOCK = { ADDRESS: 1, ARTICLE: 1, ASIDE: 1, BLOCKQUOTE: 1, CAPTION: 1, DD: 1, DETAILS: 1, DIV: 1, DL: 1, DT: 1, FIELDSET: 1, FIGCAPTION: 1, FIGURE: 1, FOOTER: 1, FORM: 1,
    H1: 1, H2: 1, H3: 1, H4: 1, H5: 1, H6: 1, HEADER: 1, HR: 1, LI: 1, MAIN: 1, NAV: 1, OL: 1, P: 1, PRE: 1, SECTION: 1, SUMMARY: 1, TABLE: 1, TBODY: 1, THEAD: 1, TFOOT: 1, TR: 1, UL: 1 };
  var LEAF = { P: 1, H1: 1, H2: 1, H3: 1, H4: 1, H5: 1, H6: 1, CAPTION: 1, FIGCAPTION: 1, PRE: 1 };
  var SKIP_SEL = 'script,style,button,input,select,textarea,svg,canvas,nav,.pagetoc,.quiz,.print-opt,.gloss-filter,.gloss-letters,.progress-big,.ra-bar,[hidden],[aria-hidden="true"]';
  var MAX_TABLE_ROWS = 40;

  function matches(el, sel) { var f = el.matches || el.msMatchesSelector || el.webkitMatchesSelector; return f.call(el, sel); }
  function cls(el, c) { return el.classList && el.classList.contains(c); }

  function edges(raw, f) { return (/^\s/.test(raw) ? ' ' : '') + f(raw) + (/\s$/.test(raw) ? ' ' : ''); }
  function inl(node, mode) {
    if (node.nodeType === 3) return edges(node.data, mode === 'formula' ? speakFormula : mode === 'code' ? speakCode : speakText);
    if (node.nodeType !== 1 || matches(node, SKIP_SEL)) return '';
    if (node.tagName === 'BR') return ' ';
    if (mode === 'text' && cls(node, 'fm')) return ' ' + speakFormula(node.textContent) + ' ';   // whole formula at once, so <sub> parts stay attached
    if (mode === 'text' && node.tagName === 'CODE') return ' ' + speakCode(node.textContent) + ' ';
    var t = '';
    for (var c = node.firstChild; c; c = c.nextSibling) t += inl(c, mode);
    return t;
  }
  function textOf(nodes) { var t = ''; for (var i = 0; i < nodes.length; i++) t += (i ? ' ' : '') + inl(nodes[i], 'text'); return tidy(t); }

  function collect(article) {
    var blocks = [];
    function push(text, els, omitted) {
      text = tidy(text);
      if (!/[A-Za-z0-9]/.test(text)) return;
      if (omitted && blocks.length && blocks[blocks.length - 1].omitted) return;
      blocks.push({ text: text, els: els, omitted: !!omitted, chunks: null });
    }
    function leafText(el) { var t = ''; for (var c = el.firstChild; c; c = c.nextSibling) t += inl(c, 'text'); t = tidy(t); if (/^H[1-6]$/.test(el.tagName) && t && !/[.!?:]$/.test(t)) t += '.'; return t; }
    function dataTable(t) {
      var rows = [].slice.call(t.querySelectorAll('tr')), heads = [];
      var hr = rows[0] && rows[0].querySelector('th') ? rows[0] : null;
      if (rows.length > MAX_TABLE_ROWS || t.querySelector('table table')) { push('Table omitted.', [t], true); return; }
      var cap = t.querySelector('caption'); if (cap) push(leafText(cap), [cap]);
      if (hr) heads = [].map.call(hr.children, function (h) { return textOf([h]); });
      rows.forEach(function (r) {
        if (r === hr) return;
        var parts = [].map.call(r.children, function (cell, i) {
          var tx = textOf([].filter.call(cell.childNodes, function (n) { return !(n.nodeType === 1 && n.tagName === 'CODE'); }));
          return tx ? ((heads[i] ? heads[i] + ': ' : '') + tx + (/[.!?]$/.test(tx) ? '' : '.')) : '';
        }).filter(Boolean);
        push(parts.join(' '), [r]);
      });
    }
    function omitOr(el) {
      if (matches(el, 'figure.fitch-fig, .fitch')) {
        var cap = el.querySelector('figcaption');
        push((cap ? 'Proof of ' + textOf([cap]) + '. ' : '') + 'Proof omitted.', [el], true);
        // keep the caption in the text but still merge consecutive omissions
        return true;
      }
      if (matches(el, '.treebox, .tree')) { push('Tree diagram omitted.', [el], true); return true; }
      if (matches(el, '.tt-wrap, table.tt')) { push('Table omitted.', [el], true); return true; }
      if (el.tagName === 'TABLE') { if (cls(el, 'data')) dataTable(el); else push('Table omitted.', [el], true); return true; }
      return false;
    }
    function walk(el) {
      var run = [], kids = el.childNodes;
      function flush() { if (run.length) { push(textOf(run), [el]); run = []; } }
      for (var i = 0; i < kids.length; i++) {
        var c = kids[i];
        if (c.nodeType === 3) { run.push(c); continue; }
        if (c.nodeType !== 1 || matches(c, SKIP_SEL)) continue;
        if (!BLOCK[c.tagName]) { run.push(c); continue; }
        flush();
        if (c.tagName === 'DT') {                               // term + its definition(s) read together
          var els = [c], txt = leafText(c), nx = c.nextElementSibling;
          if (txt && !/[.!?:]$/.test(txt)) txt += '.';
          while (nx && nx.tagName === 'DD') { els.push(nx); txt += ' ' + textOf([nx]); i = [].indexOf.call(kids, nx); nx = nx.nextElementSibling; }
          push(txt, els); continue;
        }
        handle(c);
      }
      flush();
    }
    function handle(c) {
      if (omitOr(c)) return;
      if (c.tagName === 'DETAILS') {                            // hidden solutions stay hidden; opened ones are read
        if (!c.open) return;
        [].forEach.call(c.children, function (k) { if (k.tagName !== 'SUMMARY') { if (BLOCK[k.tagName]) handle(k); } });
        return;
      }
      if (c.tagName === 'DIV' && c.querySelector(':scope > dt')) { // <div class="gloss-item"><dt>…</dt><dd>…</dd></div>
        var dt = c.querySelector(':scope > dt'), dd = [].slice.call(c.querySelectorAll(':scope > dd')), t = leafText(dt);
        if (t && !/[.!?:]$/.test(t)) t += '.';
        push(t + ' ' + textOf(dd), [c]); return;
      }
      if (LEAF[c.tagName]) { push(leafText(c), [c]); return; }
      if (c.tagName === 'HR') return;
      walk(c);
    }
    walk(article);
    return blocks;
  }

  /* ---------------------------------------------------------------- UI + speech engine */
  var RATES = [0.75, 1, 1.25, 1.5];
  var K_RATE = 'apt-ra-rate', K_VOICE = 'apt-ra-voice';
  var NO_PAGES = { search: 1, 'truth-table': 1, equivalence: 1, 'proof-checker': 1, practice: 1 };

  var memStore = {};
  function lsGet(k) {
    try { var s = root.APT_LS || root.localStorage; var v = s.getItem(k); if (v !== null && v !== undefined) return v; } catch (e) { }
    return Object.prototype.hasOwnProperty.call(memStore, k) ? memStore[k] : null;
  }
  function lsSet(k, v) {
    try { var s = root.APT_LS || root.localStorage; s.setItem(k, String(v)); return; } catch (e) { }
    memStore[k] = String(v);
  }
  function el(tag, attrs, html) {
    var e = document.createElement(tag);
    if (attrs) for (var k in attrs) e.setAttribute(k, attrs[k]);
    if (html) e.innerHTML = html;
    return e;
  }

  function init() {
    if (root.__aptRA && root.__aptRA.destroy) { try { root.__aptRA.destroy(); } catch (e) { } }
    root.__aptRA = null;
    var main = document.getElementById('main'), article = main && main.querySelector('article.content');
    var page = document.body.getAttribute('data-page');
    if (!article || cls(article, 'tool-page') || NO_PAGES[page]) return;

    var synth = null;
    try { synth = root.speechSynthesis; } catch (e) { }
    if (!synth || typeof root.SpeechSynthesisUtterance !== 'function') {
      var note = el('p', { 'class': 'ra-note', role: 'note' }, '');
      note.textContent = 'Read aloud is not available in this browser. Try Chrome, Edge, Safari or Firefox.';
      main.insertBefore(note, article);
      root.__aptRA = { destroy: function () { if (note.parentNode) note.parentNode.removeChild(note); }, unsupported: true };
      return;
    }

    var S = { blocks: null, bi: 0, ci: 0, status: 'idle', tok: 0, utt: null, watch: null, retry: 0, hl: null, voices: [], voice: null, rate: 1, listeners: [], timers: [] };
    var r = parseFloat(lsGet(K_RATE)); S.rate = RATES.indexOf(r) >= 0 ? r : 1;
    var savedVoice = lsGet(K_VOICE) || '';

    /* ---- build the bar */
    var bar = el('section', { 'class': 'ra-bar', 'aria-label': 'Read aloud', 'data-state': 'idle' });
    var rowMain = el('div', { 'class': 'ra-main' });
    var bPlay = el('button', { type: 'button', 'class': 'ra-play', 'aria-label': 'Read aloud' }, '<span class="ra-lbl">Read aloud</span>');
    var bPrev = el('button', { type: 'button', 'class': 'ra-btn ra-prev', 'aria-label': 'Previous paragraph', title: 'Previous paragraph', disabled: '' }, 'Prev');
    var bNext = el('button', { type: 'button', 'class': 'ra-btn ra-next', 'aria-label': 'Next paragraph', title: 'Next paragraph', disabled: '' }, 'Next');
    var bStop = el('button', { type: 'button', 'class': 'ra-btn ra-stop', 'aria-label': 'Stop reading', title: 'Stop', disabled: '' }, 'Stop');
    var bGear = el('button', { type: 'button', 'class': 'ra-btn ra-gear', 'aria-label': 'Speed and voice options', title: 'Speed and voice', 'aria-expanded': 'false', 'aria-controls': 'ra-opts' }, 'Options');
    [bPlay, bPrev, bNext, bStop, bGear].forEach(function (b) { rowMain.appendChild(b); });
    var opts = el('div', { 'class': 'ra-opts', id: 'ra-opts' });
    var lRate = el('label', { 'class': 'ra-field' }, '<span>Speed</span>'), sRate = el('select', { 'class': 'ra-rate', 'aria-label': 'Reading speed' });
    RATES.forEach(function (v) { var o = el('option', { value: String(v) }); o.textContent = v + '×'; if (v === S.rate) o.selected = true; sRate.appendChild(o); });
    lRate.appendChild(sRate);
    var lVoice = el('label', { 'class': 'ra-field ra-field-voice' }, '<span>Voice</span>'), sVoice = el('select', { 'class': 'ra-voice', 'aria-label': 'Voice' });
    lVoice.appendChild(sVoice);
    opts.appendChild(lRate); opts.appendChild(lVoice);
    var status = el('p', { 'class': 'ra-status' }); status.setAttribute('aria-live', 'off');
    bar.appendChild(rowMain); bar.appendChild(opts); bar.appendChild(status);
    main.insertBefore(bar, article);
    document.documentElement.classList.add('has-ra');

    /* ---- helpers */
    function on(target, type, fn, o) { target.addEventListener(type, fn, o); S.listeners.push([target, type, fn, o]); }
    function later(fn, ms) { var id = setTimeout(fn, ms); S.timers.push(id); return id; }
    function blocks() { if (!S.blocks) S.blocks = collect(article); return S.blocks; }
    function langOf(v) { return String(v.lang || '').replace('_', '-').toLowerCase(); }
    function voiceKey(v) { return v.voiceURI || v.name; }

    function loadVoices() {
      var all = []; try { all = [].slice.call(synth.getVoices() || []); } catch (e) { }
      var en = all.filter(function (v) { return langOf(v).indexOf('en') === 0; });
      var gb = en.filter(function (v) { return langOf(v) === 'en-gb'; }), other = en.filter(function (v) { return langOf(v) !== 'en-gb'; });
      var list = en.length ? gb.concat(other) : all;
      var key = list.map(voiceKey).join('|');
      if (key === S.voiceKey) return; S.voiceKey = key;
      S.voices = list; sVoice.innerHTML = '';
      var auto = el('option', { value: '' }); auto.textContent = list.length ? 'Automatic (' + (gb.length ? 'British English' : 'English') + ')' : 'Default voice'; sVoice.appendChild(auto);
      list.forEach(function (v) { var o = el('option', { value: voiceKey(v) }); o.textContent = v.name + ' (' + String(v.lang || '').replace('_', '-') + ')'; sVoice.appendChild(o); });
      if (savedVoice && list.some(function (v) { return voiceKey(v) === savedVoice; })) sVoice.value = savedVoice; else sVoice.value = '';
      pickVoice();
    }
    function pickVoice() {
      var k = sVoice.value, v = null;
      if (k) S.voices.forEach(function (x) { if (voiceKey(x) === k) v = x; });
      if (!v && S.voices.length) {
        var pref = S.voices.filter(function (x) { return langOf(x) === 'en-gb'; });
        v = pref.filter(function (x) { return /natural|neural|premium|enhanced|online/i.test(x.name); })[0] || pref[0] || S.voices[0];
      }
      S.voice = v;
    }
    loadVoices();
    if (typeof synth.addEventListener === 'function') on(synth, 'voiceschanged', loadVoices);
    [250, 800, 2000, 4000].forEach(function (ms) { later(loadVoices, ms); });

    function clearHl() { if (S.hl) { S.hl.forEach(function (e) { e.classList.remove('ra-current'); }); S.hl = null; } }
    function setHl(i) {
      var b = blocks()[i]; clearHl(); if (!b) return;
      b.els.forEach(function (e) { e.classList.add('ra-current'); }); S.hl = b.els;
      var e0 = b.els[0], rc = e0.getBoundingClientRect(), bb = bar.getBoundingClientRect(), vh = root.innerHeight || document.documentElement.clientHeight;
      var top = Math.max(bb.bottom, 0) + 8, tall = rc.height > (vh - top) * 0.8;
      var ok = rc.top >= top && (tall ? rc.top < vh * 0.5 : rc.bottom <= vh - 8);
      if (!ok) {
        var reduce = false; try { reduce = root.matchMedia('(prefers-reduced-motion: reduce)').matches; } catch (e) { }
        try { e0.scrollIntoView({ block: tall ? 'start' : 'center', behavior: reduce ? 'auto' : 'smooth' }); } catch (e) { e0.scrollIntoView(true); }
      }
    }

    function ui() {
      var st = S.status, n = blocks().length;
      bar.setAttribute('data-state', st);
      var lbl = bPlay.querySelector('.ra-lbl');
      var txt = st === 'playing' ? 'Pause' : st === 'paused' ? 'Resume' : 'Read aloud';
      lbl.textContent = txt; bPlay.setAttribute('aria-label', st === 'playing' ? 'Pause reading' : st === 'paused' ? 'Resume reading' : 'Read aloud');
      bPlay.setAttribute('aria-pressed', st === 'playing' ? 'true' : 'false');
      var active = st !== 'idle';
      bPrev.disabled = bNext.disabled = bStop.disabled = !active;
      status.textContent = st === 'idle' ? (S.done ? 'Finished reading this page.' : '') : (st === 'paused' ? 'Paused · ' : '') + 'Paragraph ' + Math.min(S.bi + 1, n) + ' of ' + n;
    }

    function cancelSpeech() { try { synth.cancel(); } catch (e) { } }
    function clearWatch() { if (S.watch) { clearTimeout(S.watch); S.watch = null; } }
    function invalidate() { S.tok++; clearWatch(); S.utt = null; }

    function speakChunk(fresh) {
      var bl = blocks();
      while (S.bi < bl.length) {
        var b = bl[S.bi]; if (!b.chunks) b.chunks = chunk(b.text);
        if (S.ci < b.chunks.length) break;
        S.bi++; S.ci = 0;
      }
      if (S.bi >= bl.length) { finish(true); return; }
      var b2 = bl[S.bi], text = b2.chunks[S.ci], tok = ++S.tok;
      if (S.hlIndex !== S.bi) { S.hlIndex = S.bi; setHl(S.bi); }
      ui();
      var u = new root.SpeechSynthesisUtterance(text);
      u.lang = (S.voice && S.voice.lang) || 'en-GB'; if (S.voice) u.voice = S.voice;
      u.rate = S.rate; u.pitch = 1; u.volume = 1;
      u.onstart = function () { if (tok === S.tok) S.started = true; };
      u.onend = function () { if (tok !== S.tok) return; clearWatch(); S.retry = 0; S.ci++; speakChunk(false); };
      u.onerror = function (ev) {
        if (tok !== S.tok) return;
        var er = ev && ev.error;
        if (er === 'canceled' || er === 'interrupted') return;
        clearWatch();
        if (er === 'not-allowed') { stop(); status.textContent = 'Your browser blocked speech. Tap Read aloud again.'; return; }
        if (S.retry < 1) { S.retry++; later(function () { if (tok === S.tok && S.status === 'playing') speakChunk(true); }, 150); }
        else { S.retry = 0; S.ci++; speakChunk(false); }
      };
      S.utt = u; S.started = false;           // keep a reference: Chrome can garbage-collect a speaking utterance and never fire onend
      // watchdog for engines that silently stall (Chrome's long-utterance cut-off, Android voices that never start)
      var ms = Math.max(7000, (text.length / (12 * S.rate)) * 1000 * 1.8 + 4000);
      clearWatch();
      S.watch = setTimeout(function () {
        if (tok !== S.tok || S.status !== 'playing') return;
        cancelSpeech(); S.retry = 0; S.ci++; speakChunk(true);
      }, ms);
      var busy = false; try { busy = synth.speaking || synth.pending; } catch (e) { }
      var go = function () {
        if (tok !== S.tok || S.status !== 'playing') return;
        try { if (synth.paused) synth.resume(); } catch (e) { }
        try { synth.speak(u); } catch (e) { }
      };
      if (fresh && busy) { cancelSpeech(); later(go, 70); }  // Android/Chrome drop a speak() that immediately follows cancel()
      else go();
    }
    function finish(done) {
      invalidate(); cancelSpeech(); S.status = 'idle'; S.bi = 0; S.ci = 0; S.hlIndex = -1; S.done = !!done; clearHl(); ui();
    }
    function firstVisibleBlock() {
      var bl = blocks(), bb = bar.getBoundingClientRect();
      if ((root.pageYOffset || document.documentElement.scrollTop || 0) < 120) return 0;
      for (var i = 0; i < bl.length; i++) { if (bl[i].els[0].getBoundingClientRect().top >= bb.bottom - 2) return i; }
      return 0;
    }
    function start() {
      if (!blocks().length) { status.textContent = 'Nothing to read on this page.'; return; }
      S.done = false; S.bi = firstVisibleBlock(); S.ci = 0; S.hlIndex = -1; S.retry = 0; S.status = 'playing';
      invalidate(); speakChunk(true);
    }
    function pause() { if (S.status !== 'playing') return; S.status = 'paused'; invalidate(); cancelSpeech(); ui(); }   // cancel + re-speak is the only pause that works on Android
    function resume() { if (S.status !== 'paused') return; S.status = 'playing'; invalidate(); speakChunk(true); }
    function stop() { finish(false); }
    function go(delta) {
      if (S.status === 'idle') return;
      var n = blocks().length, ni = S.bi + delta;
      if (ni >= n) { finish(true); return; }
      S.bi = Math.max(0, ni); S.ci = 0; S.retry = 0; S.hlIndex = S.bi;
      invalidate(); setHl(S.bi); ui();
      if (S.status === 'playing') { cancelSpeech(); speakChunk(true); } else cancelSpeech();
    }
    function restartCurrent() { if (S.status === 'playing') { invalidate(); cancelSpeech(); speakChunk(true); } }

    /* ---- events */
    on(bPlay, 'click', function () { if (S.status === 'idle') start(); else if (S.status === 'playing') pause(); else resume(); });
    on(bStop, 'click', stop);
    on(bPrev, 'click', function () { go(-1); });
    on(bNext, 'click', function () { go(1); });
    on(bGear, 'click', function () { var o = bar.classList.toggle('ra-open'); bGear.setAttribute('aria-expanded', o ? 'true' : 'false'); });
    on(sRate, 'change', function () { S.rate = parseFloat(sRate.value) || 1; lsSet(K_RATE, S.rate); restartCurrent(); });
    on(sVoice, 'change', function () { savedVoice = sVoice.value; lsSet(K_VOICE, savedVoice); pickVoice(); restartCurrent(); });
    var halt = function () { invalidate(); cancelSpeech(); };
    on(root, 'pagehide', halt); on(root, 'beforeunload', halt);

    function destroy() {
      invalidate(); cancelSpeech(); S.status = 'idle';
      S.timers.forEach(clearTimeout); S.timers = [];
      S.listeners.forEach(function (l) { try { l[0].removeEventListener(l[1], l[2], l[3]); } catch (e) { } }); S.listeners = [];
      clearHl();
      if (bar.parentNode) bar.parentNode.removeChild(bar);
      document.documentElement.classList.remove('has-ra');
    }
    ui();
    root.__aptRA = { destroy: destroy, state: S, bar: bar, blocks: blocks, API: API };
  }

  init();
})(typeof window !== 'undefined' ? window : this);
