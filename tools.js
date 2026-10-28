/* tools.js — truth-table generator, equivalence checker and Fitch proof checker UIs. Requires logic.js. */
(function () {
  'use strict';
  var L = window.Logic;
  function $(s, r) { return (r || document).querySelector(s); }
  function $$(s, r) { return Array.prototype.slice.call((r || document).querySelectorAll(s)); }
  function esc(s) { return String(s).replace(/[&<>"]/g, function (c) { return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]; }); }
  function tf(b, cls) { return '<td class="' + (b ? 't' : 'f') + (cls ? ' ' + cls : '') + '">' + (b ? 'T' : 'F') + '</td>'; }
  function errBox(e, input) {
    var pos = (e && typeof e.pos === 'number') ? e.pos : null, h = '<div class="msg bad" role="alert"><strong>Error:</strong> ' + esc(e.message || e);
    if (pos !== null && input) h += '<br><code>' + esc(input.slice(0, pos)) + '<mark>' + esc(input.slice(pos, pos + 1) || ' ') + '</mark>' + esc(input.slice(pos + 1)) + '</code>';
    return h + '</div>';
  }
  /* Symbol buttons insert at the cursor of the associated input */
  if (!window.__toolsInit) { window.__toolsInit = true; document.addEventListener('focusin', function (e) { if (e.target.matches && e.target.matches('input[type=text]')) window.__aptLastInput = e.target; }); }
  function getLast() { var x = window.__aptLastInput; return x && document.body.contains(x) ? x : null; }
  $$('.symbar').forEach(function (bar) {
    bar.addEventListener('mousedown', function (e) { if (e.target.closest('button')) e.preventDefault(); });
    bar.addEventListener('click', function (e) {
      var b = e.target.closest('button'); if (!b) return;
      var target = bar.getAttribute('data-for') ? document.getElementById(bar.getAttribute('data-for')) : getLast();
      if (!target || (bar.getAttribute('data-for') === null && !getLast())) target = getLast() || $('input[type=text]');
      if (!target) return;
      var s = target.selectionStart != null ? target.selectionStart : target.value.length, en = target.selectionEnd != null ? target.selectionEnd : s, ins = b.getAttribute('data-ins');
      target.value = target.value.slice(0, s) + ins + target.value.slice(en);
      target.focus(); target.setSelectionRange(s + ins.length, s + ins.length);
      target.dispatchEvent(new Event('input'));
    });
  });

  /* ---------- Truth-table generator ---------- */
  var ttIn = $('#tt-in');
  if (ttIn) {
    var ttOut = $('#tt-out');
    var runTT = function () {
      var s = ttIn.value.trim();
      if (!s) { ttOut.innerHTML = '<div class="msg info">Type a formula or an argument above.</div>'; return; }
      try {
        var arg = L.splitArgument(s);
        if (arg) {
          if (!arg.conclusion.trim()) throw L.LogicError('There is no conclusion after the "therefore" sign.');
          var P = arg.premises.map(function (p, k) { try { return L.parse(p); } catch (e) { e.message = 'Premise ' + (k + 1) + ': ' + e.message; throw e; } });
          var C; try { C = L.parse(arg.conclusion); } catch (e) { e.message = 'Conclusion: ' + e.message; throw e; }
          var r = L.checkArgument(P, C);
          var h = r.valid
            ? '<div class="msg ok" role="status"><strong>Valid.</strong> There is no row in which every premise is true and the conclusion false.' + (r.rows.some(function (x) { return x.prem.every(Boolean); }) ? '' : ' (In fact the premises are never all true together, so the argument is valid vacuously.)') + '</div>'
            : '<div class="msg bad" role="status"><strong>Invalid.</strong> ' + r.counterexamples.length + ' counterexample row' + (r.counterexamples.length > 1 ? 's' : '') + ' (highlighted): e.g. ' + r.atoms.map(function (a) { return a + ' = ' + (r.counterexamples[0].v[a] ? 'T' : 'F'); }).join(', ') + ' makes every premise true and the conclusion false.</div>';
          h += '<div class="tt-wrap"><table class="tt"><thead><tr>' + r.atoms.map(function (a) { return '<th scope="col">' + esc(a) + '</th>'; }).join('') +
            r.premises.map(function (p, k) { return '<th scope="col" class="sep" title="Premise ' + (k + 1) + '">' + esc(L.show(p)) + '</th>'; }).join('') + '<th scope="col" class="main sep">∴ ' + esc(L.show(r.conclusion)) + '</th><th></th></tr></thead><tbody>';
          r.rows.forEach(function (row) {
            var bad = row.prem.every(Boolean) && !row.concl;
            h += '<tr class="' + (bad ? 'counter' : (row.prem.every(Boolean) ? 'allprem' : '')) + '">' + r.atoms.map(function (a) { return tf(row.v[a]); }).join('') + row.prem.map(function (b) { return tf(b, 'sep'); }).join('') + tf(row.concl, 'main sep') + '<td class="note">' + (bad ? '← counterexample' : '') + '</td></tr>';
          });
          h += '</tbody></table></div><p class="tool-help">Green rows: all premises true. Red rows: all premises true and conclusion false.</p>';
          ttOut.innerHTML = h;
        } else {
          var t = L.truthTable(s);
          var label = { tautology: 'a <strong>tautology</strong> (true in every row)', contradiction: 'a <strong>contradiction</strong> (false in every row)', contingent: '<strong>contingent</strong> (true in some rows, false in others)' }[t.classification];
          var h2 = '<div class="msg ' + (t.classification === 'contradiction' ? 'bad' : t.classification === 'tautology' ? 'ok' : 'info') + '" role="status">Read as <span class="fm">' + esc(L.show(t.formula)) + '</span>' + (L.mainConnective(t.formula) ? '' : '') + '. This formula is ' + label + '.</div>';
          h2 += '<div class="tt-wrap"><table class="tt"><thead><tr>' + t.atoms.map(function (a) { return '<th scope="col">' + esc(a) + '</th>'; }).join('') +
            t.columns.map(function (c, k) { return '<th scope="col" class="' + (k === 0 ? 'sep ' : '') + (k === t.columns.length - 1 ? 'main' : '') + '">' + esc(L.show(c)) + '</th>'; }).join('') + '</tr></thead><tbody>';
          t.rows.forEach(function (row) {
            h2 += '<tr>' + t.atoms.map(function (a) { return tf(row.v[a]); }).join('') + row.vals.map(function (v, k) { return tf(v, (k === 0 ? 'sep ' : '') + (k === row.vals.length - 1 ? 'main' : '')); }).join('') + '</tr>';
          });
          if (!t.columns.length) h2 = '<div class="msg info">A single sentence letter is contingent: it is true in one row and false in the other.</div>';
          ttOut.innerHTML = h2 + '</tbody></table></div><p class="tool-help">Columns are the subformulas, built up from the inside out; the shaded column is the whole formula.</p>';
        }
      } catch (e) { ttOut.innerHTML = errBox(e, s); }
    };
    $('#tt-go').addEventListener('click', runTT);
    ttIn.addEventListener('keydown', function (e) { if (e.key === 'Enter') runTT(); });
    $$('[data-ex]').forEach(function (b) { b.addEventListener('click', function () { ttIn.value = b.getAttribute('data-ex'); runTT(); }); });
    var q = new URLSearchParams(window.APT_QS ? window.APT_QS() : location.search).get('f'); if (q) { ttIn.value = q; runTT(); }
  }

  /* ---------- Equivalence / entailment ---------- */
  var eqA = $('#eq-a');
  if (eqA) {
    var eqB = $('#eq-b'), eqOut = $('#eq-out');
    var runEq = function () {
      var a = eqA.value.trim(), b = eqB.value.trim();
      if (!a || !b) { eqOut.innerHTML = '<div class="msg info">Enter two formulas.</div>'; return; }
      var A, B;
      try { A = L.parse(a); } catch (e) { eqOut.innerHTML = errBox({ message: 'Formula A: ' + e.message, pos: e.pos }, a); return; }
      try { B = L.parse(b); } catch (e) { eqOut.innerHTML = errBox({ message: 'Formula B: ' + e.message, pos: e.pos }, b); return; }
      try {
        var c = L.compare(A, B), sa = esc(L.show(A)), sb = esc(L.show(B)), h;
        if (c.equivalent) h = '<div class="msg ok" role="status"><strong>Equivalent.</strong> <span class="fm">' + sa + '</span> and <span class="fm">' + sb + '</span> have the same truth value in every row, so each entails the other.</div>';
        else if (c.aEntailsB) h = '<div class="msg info" role="status"><strong>Not equivalent, but A entails B.</strong> Every row making <span class="fm">' + sa + '</span> true makes <span class="fm">' + sb + '</span> true, but not conversely (see highlighted rows).</div>';
        else if (c.bEntailsA) h = '<div class="msg info" role="status"><strong>Not equivalent, but B entails A.</strong> Every row making <span class="fm">' + sb + '</span> true makes <span class="fm">' + sa + '</span> true, but not conversely (see highlighted rows).</div>';
        else h = '<div class="msg bad" role="status"><strong>Neither entails the other.</strong> There are rows where A is true and B false, and rows where B is true and A false (highlighted).</div>';
        h += '<div class="tt-wrap"><table class="tt"><thead><tr>' + c.atoms.map(function (x) { return '<th scope="col">' + esc(x) + '</th>'; }).join('') + '<th scope="col" class="sep">A: ' + sa + '</th><th scope="col" class="sep">B: ' + sb + '</th><th></th></tr></thead><tbody>';
        c.rows.forEach(function (r) { var d = r.a !== r.b; h += '<tr class="' + (d ? 'counter' : '') + '">' + c.atoms.map(function (x) { return tf(r.v[x]); }).join('') + tf(r.a, 'sep') + tf(r.b, 'sep') + '<td class="note">' + (d ? (r.a ? '← A true, B false' : '← B true, A false') : '') + '</td></tr>'; });
        eqOut.innerHTML = h + '</tbody></table></div>';
      } catch (e) { eqOut.innerHTML = errBox(e); }
    };
    $('#eq-go').addEventListener('click', runEq);
    [eqA, eqB].forEach(function (i) { i.addEventListener('keydown', function (e) { if (e.key === 'Enter') runEq(); }); });
    $$('[data-eq]').forEach(function (b) { b.addEventListener('click', function () { var p = b.getAttribute('data-eq').split('||'); eqA.value = p[0]; eqB.value = p[1]; runEq(); }); });
  }

  /* ---------- Proof checker ---------- */
  var pcBody = $('#pc-body');
  if (pcBody) {
    var rows = [], problem = null, SAVE = 'apt-proof-v1';
    var sel = $('#pc-problem'), premIn = $('#pc-prem'), goalIn = $('#pc-goal'), out = $('#pc-out'), derived = $('#pc-derived');
    (window.PC_PROBLEMS || []).forEach(function (p) {
      var o = document.createElement('option'); o.value = p.id;
      o.textContent = p.level + ': ' + p.title + ' — ' + (p.premises.length ? p.premises.join(', ') + ' ' : '') + '⊢ ' + p.conclusion;
      sel.appendChild(o);
    });
    function save() { try { (window.APT_LS || localStorage).setItem(SAVE, JSON.stringify({ rows: rows, prem: premIn.value, goal: goalIn.value, pid: problem ? problem.id : '' })); } catch (e) { } }
    function render(focusIdx, focusField) {
      var h = '';
      rows.forEach(function (r, k) {
        var bars = ''; for (var q = 0; q <= r.d; q++) bars += '<span></span>';
        h += '<tr data-k="' + k + '" class="' + (r.st || '') + '"><td class="pc-num">' + (k + 1) + '</td>' +
          '<td class="pc-depth"><button type="button" class="dl" aria-label="Line ' + (k + 1) + ': decrease depth" title="Outdent (close subproof)">◂</button> <button type="button" class="dr" aria-label="Line ' + (k + 1) + ': increase depth" title="Indent (subproof)">▸</button></td>' +
          '<td class="pc-f"><div class="pc-formula-cell"><span class="pc-bars" aria-hidden="true">' + bars + '</span><label class="sr-only" for="pcf' + k + '">Line ' + (k + 1) + ' formula</label><input type="text" id="pcf' + k + '" class="f" value="' + esc(r.f) + '" spellcheck="false" autocomplete="off"></div></td>' +
          '<td class="pc-j"><label class="sr-only" for="pcj' + k + '">Line ' + (k + 1) + ' justification</label><input type="text" id="pcj' + k + '" class="j" value="' + esc(r.j) + '" placeholder="rule lines" spellcheck="false" autocomplete="off"></td>' +
          '<td class="pc-status" aria-label="' + (r.st === 'ok' ? 'correct' : r.st === 'err' ? 'error' : '') + '">' + (r.st === 'ok' ? '✓' : r.st === 'err' ? '✗' : '') + '</td>' +
          '<td class="pc-tools"><button type="button" class="ins" aria-label="Insert line after ' + (k + 1) + '" title="Insert line below">+</button> <button type="button" class="del" aria-label="Delete line ' + (k + 1) + '" title="Delete line">×</button></td></tr>';
        if (r.st === 'err' && r.msg) h += '<tr class="pc-msg"><td colspan="6">Line ' + (k + 1) + ': ' + esc(r.msg) + '</td></tr>';
      });
      pcBody.innerHTML = h || '<tr><td colspan="6" class="tool-help">No lines yet. Choose an exercise or type premises and press “Start”.</td></tr>';
      if (focusIdx != null) { var el = $('#pc' + (focusField || 'f') + focusIdx); if (el) { el.focus(); } }
      save();
    }
    function clearStatus() { rows.forEach(function (r) { r.st = ''; r.msg = ''; }); out.innerHTML = ''; }
    pcBody.addEventListener('input', function (e) {
      var tr = e.target.closest('tr[data-k]'); if (!tr) return; var r = rows[+tr.getAttribute('data-k')];
      if (e.target.classList.contains('f')) r.f = e.target.value; else r.j = e.target.value;
      if (r.st) { r.st = ''; tr.className = ''; tr.querySelector('.pc-status').textContent = ''; }
      save();
    });
    pcBody.addEventListener('click', function (e) {
      var b = e.target.closest('button'); if (!b) return; var tr = b.closest('tr[data-k]'), k = +tr.getAttribute('data-k');
      if (b.classList.contains('dl')) { rows[k].d = Math.max(0, rows[k].d - 1); clearStatus(); render(); $('#pcf' + k) && $$('.dl', pcBody)[k].focus(); }
      else if (b.classList.contains('dr')) { rows[k].d = Math.min(8, rows[k].d + 1); clearStatus(); render(); $$('.dr', pcBody)[k].focus(); }
      else if (b.classList.contains('ins')) { rows.splice(k + 1, 0, { f: '', j: '', d: rows[k].d }); clearStatus(); render(k + 1); }
      else if (b.classList.contains('del')) { rows.splice(k, 1); clearStatus(); render(Math.min(k, rows.length - 1)); }
    });
    pcBody.addEventListener('keydown', function (e) {
      var tr = e.target.closest('tr[data-k]'); if (!tr) return; var k = +tr.getAttribute('data-k');
      if (e.key === 'Enter') { e.preventDefault(); if (e.target.classList.contains('f')) { $('#pcj' + k).focus(); } else { rows.splice(k + 1, 0, { f: '', j: '', d: rows[k].d }); clearStatus(); render(k + 1); } }
      if (e.key === 'Tab' && e.altKey) { e.preventDefault(); rows[k].d = Math.max(0, rows[k].d + (e.shiftKey ? -1 : 1)); render(k); }
    });
    function setup(prem, goal, pid) {
      problem = pid ? (window.PC_PROBLEMS || []).filter(function (p) { return p.id === pid; })[0] : null;
      premIn.value = prem.join(', '); goalIn.value = goal;
      rows = prem.map(function (p) { return { f: L.pretty(p), j: 'PR', d: 0 }; });
      rows.push({ f: '', j: '', d: 0 });
      $('#pc-solution').disabled = !(problem && problem.solution);
      out.innerHTML = '<div class="msg info">Goal: <span class="fm">' + esc(prem.map(L.pretty).join(', ') + (prem.length ? ' ' : '') + '⊢ ' + L.pretty(goal)) + '</span>. Add lines, then press “Check proof”.</div>';
      render(rows.length - 1);
    }
    sel.addEventListener('change', function () {
      var p = (window.PC_PROBLEMS || []).filter(function (x) { return x.id === sel.value; })[0];
      if (p) setup(p.premises, p.conclusion, p.id);
    });
    $('#pc-start').addEventListener('click', function () {
      var goal = goalIn.value.trim();
      if (!goal) { out.innerHTML = '<div class="msg bad">Enter a goal (conclusion) first.</div>'; return; }
      var prem = L.splitTop(premIn.value);
      for (var k = 0; k < prem.length; k++) { try { L.parse(prem[k]); } catch (e) { out.innerHTML = errBox({ message: 'Premise ' + (k + 1) + ': ' + e.message }); return; } }
      try { L.parse(goal); } catch (e) { out.innerHTML = errBox({ message: 'Goal: ' + e.message }); return; }
      sel.value = ''; setup(prem, goal, null);
    });
    $('#pc-add').addEventListener('click', function () { var d = rows.length ? rows[rows.length - 1].d : 0; rows.push({ f: '', j: '', d: d }); clearStatus(); render(rows.length - 1); });
    $('#pc-assume').addEventListener('click', function () { var d = rows.length ? rows[rows.length - 1].d : 0; rows.push({ f: '', j: 'AS', d: d + 1 }); clearStatus(); render(rows.length - 1); });
    $('#pc-clear').addEventListener('click', function () { if (!rows.length || window.confirm('Remove all lines?')) { rows = []; out.innerHTML = ''; render(); } });
    $('#pc-solution').addEventListener('click', function () {
      if (!problem || !problem.solution) return;
      if (!window.confirm('Replace your lines with a model solution?')) return;
      rows = L.parseProofText(problem.solution).map(function (r) { return { f: r.f, j: r.j, d: r.d }; }); check();
    });
    function check() {
      var lines = rows.filter(function (r) { return r.f.trim() || r.j.trim(); });
      if (lines.length !== rows.length) rows = lines;
      var goal = goalIn.value.trim(), prem = L.splitTop(premIn.value);
      var res = L.checkProof(rows, { premises: prem, conclusion: goal || null, allowDerived: derived.checked });
      rows.forEach(function (r, k) { r.st = res.lines[k].ok ? 'ok' : 'err'; r.msg = res.lines[k].msg; if (res.lines[k].ok && res.lines[k].formula) r.f = res.lines[k].formula; });
      render();
      out.innerHTML = '<div class="msg ' + (res.complete ? 'ok' : (res.ok ? 'info' : 'bad')) + '" role="status">' + esc(res.summary) + '</div>';
    }
    $('#pc-check').addEventListener('click', check);
    $('#pc-export').addEventListener('click', function () {
      $('#pc-text').value = (goalIn.value ? '% ' + premIn.value + (premIn.value ? ' ' : '') + '⊢ ' + goalIn.value + '\n' : '') + rows.map(function (r) { return Array(r.d + 1).join('| ') + r.f + ' ; ' + r.j; }).join('\n');
      $('#pc-text').focus();
    });
    $('#pc-import').addEventListener('click', function () {
      var txt = $('#pc-text').value, g = txt.split('\n').filter(function (l) { return /^\s*%/.test(l); })[0];
      if (g) { var parts = g.replace(/^\s*%\s*/, '').split(/\s*(?:⊢|\|-)\s*/); goalIn.value = parts[parts.length - 1]; premIn.value = parts.length > 1 ? parts[0] : ''; }
      rows = L.parseProofText(txt).map(function (r) { return { f: r.f, j: r.j, d: r.d }; }); clearStatus(); render();
    });
    try {
      var saved = JSON.parse((window.APT_LS || localStorage).getItem(SAVE) || 'null');
      if (saved && saved.rows && saved.rows.length) { rows = saved.rows; premIn.value = saved.prem || ''; goalIn.value = saved.goal || ''; problem = (window.PC_PROBLEMS || []).filter(function (p) { return p.id === saved.pid; })[0] || null; if (problem) sel.value = problem.id; $('#pc-solution').disabled = !(problem && problem.solution); clearStatus(); render(); }
      else { sel.value = 'p1'; sel.dispatchEvent(new Event('change')); }
    } catch (e) { render(); }
  }
})();
