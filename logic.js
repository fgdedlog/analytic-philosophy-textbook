/* logic.js — parser, evaluator, truth tables, models and a Fitch-style proof checker.
   Original code for "Analytic Philosophy: An Introduction with Symbolic Logic". No dependencies.
   Works in the browser (window.Logic) and in Node (module.exports). */
(function (root) {
  'use strict';

  function LogicError(msg, pos) { var e = new Error(msg); e.name = 'LogicError'; e.pos = pos; return e; }
  function isVar(t) { return /^[tuwxyz][0-9']*$/.test(t); }

  /* ---------------- Lexer ---------------- */
  var CLOSE = { '(': ')', '[': ']', '{': '}' };
  function lex(s) {
    var toks = [], i = 0, n = s.length, m;
    function push(k, len, v) { toks.push({ k: k, v: v || s.substr(i, len), pos: i, end: i + len }); i += len; }
    while (i < n) {
      var c = s[i], rest = s.slice(i);
      if (/\s/.test(c)) { i++; continue; }
      if ((m = rest.match(/^(<->|<=>|↔|≡|⟷)/))) { push('iff', m[0].length, '↔'); continue; }
      if ((m = rest.match(/^(->|=>|→|⊃|⟶)/))) { push('imp', m[0].length, '→'); continue; }
      if ((m = rest.match(/^(_\|_|⊥|#)/))) { push('bot', m[0].length, '⊥'); continue; }
      if ((m = rest.match(/^(!=|≠)/))) { push('neq', m[0].length, '≠'); continue; }
      if ((m = rest.match(/^(forall|exists)(?![A-Za-z])/))) { push(m[0] === 'forall' ? 'all' : 'ex', m[0].length, m[0] === 'forall' ? '∀' : '∃'); continue; }
      if (/[¬~!−-]/.test(c)) { push('not', 1, '¬'); continue; }
      if (/[∧&^]/.test(c)) { push('and', 1, '∧'); continue; }
      if (/[∨|v]/.test(c)) { push('or', 1, '∨'); continue; }
      if (c === '∀') { push('all', 1); continue; }
      if (c === '∃') { push('ex', 1); continue; }
      if (c === '=') { push('eq', 1); continue; }
      if (/[(\[{]/.test(c)) { push('lp', 1); continue; }
      if (/[)\]}]/.test(c)) { push('rp', 1); continue; }
      if (c === ',') { push('comma', 1); continue; }
      if ((m = rest.match(/^[A-Z][0-9']*/))) { push('upper', m[0].length); continue; }
      if ((m = rest.match(/^[a-z][0-9']*/))) { push('lower', m[0].length); continue; }
      throw LogicError('Unknown symbol "' + c + '" at character ' + (i + 1) + '. Use letters, ¬ ∧ ∨ → ↔ (or ~ & v -> <->), brackets' + ' and, for predicate logic, ∀ ∃ =.', i);
    }
    return toks;
  }

  /* ---------------- Parser ----------------
     Precedence (tightest first): ¬, quantifiers  >  ∧  >  ∨  >  →  >  ↔
     ∧ and ∨ group to the left; → and ↔ group to the right. */
  function parse(s) {
    if (typeof s !== 'string') throw LogicError('No formula given.', 0);
    var toks = lex(s), i = 0;
    if (!toks.length) throw LogicError('The formula is empty.', 0);
    function peek() { return toks[i]; }
    function where(t) { return t ? ' at character ' + (t.pos + 1) : ' at the end'; }
    function describe(t) {
      if (!t) return 'the end of the formula';
      return '"' + t.v + '"';
    }
    function needOperand(op) {
      var t = peek();
      if (!t) throw LogicError('The formula ends after "' + op.v + '": a formula is needed after it.', s.length);
    }
    function pIff() {
      var l = pImp(), t = peek();
      if (t && t.k === 'iff') { i++; needOperand(t); return { t: 'iff', a: l, b: pIff() }; }
      return l;
    }
    function pImp() {
      var l = pOr(), t = peek();
      if (t && t.k === 'imp') { i++; needOperand(t); return { t: 'imp', a: l, b: pImp() }; }
      return l;
    }
    function pOr() {
      var l = pAnd(), t;
      while ((t = peek()) && t.k === 'or') { i++; needOperand(t); l = { t: 'or', a: l, b: pAnd() }; }
      return l;
    }
    function pAnd() {
      var l = pUnary(), t;
      while ((t = peek()) && t.k === 'and') { i++; needOperand(t); l = { t: 'and', a: l, b: pUnary() }; }
      return l;
    }
    function pUnary() {
      var t = peek();
      if (!t) throw LogicError('The formula ends too early: expected a sentence letter, ¬, a quantifier or "(".', s.length);
      switch (t.k) {
        case 'not': i++; needOperand(t); return { t: 'not', a: pUnary() };
        case 'all': case 'ex': {
          i++; var v = peek();
          if (!v || v.k !== 'lower' || !isVar(v.v)) throw LogicError('Expected a variable (t, u, w, x, y or z) after ' + t.v + where(v) + '.', v ? v.pos : s.length);
          i++; needOperand(v);
          return { t: t.k, v: v.v, a: pUnary() };
        }
        case 'lp': {
          i++;
          if (peek() && peek().k === 'rp') throw LogicError('Empty brackets "' + t.v + peek().v + '"' + where(t) + '.', t.pos);
          var f = pIff(), c = peek();
          if (!c) throw LogicError('Missing closing bracket for the "' + t.v + '" at character ' + (t.pos + 1) + '.', s.length);
          if (c.k !== 'rp') throw LogicError('Expected a connective or ")"' + where(c) + ' but found ' + describe(c) + '. (Two formulas cannot simply sit side by side.)', c.pos);
          if (c.v !== CLOSE[t.v]) throw LogicError('Mismatched brackets: "' + t.v + '" at character ' + (t.pos + 1) + ' is closed by "' + c.v + '".', c.pos);
          i++; return f;
        }
        case 'bot': i++; return { t: 'bot' };
        case 'upper': {
          i++; var args = [], end = t.end, a;
          while ((a = peek()) && a.k === 'lower' && a.pos === end) { args.push(a.v); end = a.end; i++; }
          return { t: 'pred', n: t.v, args: args };
        }
        case 'lower': {
          var nx = toks[i + 1];
          if (nx && (nx.k === 'eq' || nx.k === 'neq')) {
            var r = toks[i + 2];
            if (!r || r.k !== 'lower') throw LogicError('Expected a name or variable after "' + nx.v + '"' + where(r) + '.', r ? r.pos : s.length);
            i += 3; var e = { t: 'eq', l: t.v, r: r.v };
            return nx.k === 'neq' ? { t: 'not', a: e } : e;
          }
          if (t.v === 'v') throw LogicError('"v" is reserved for "or".', t.pos);
          i++; return { t: 'pred', n: t.v, args: [] };
        }
        case 'rp': throw LogicError('Unexpected closing bracket "' + t.v + '"' + where(t) + '.', t.pos);
        case 'eq': case 'neq': throw LogicError('"' + t.v + '"' + where(t) + ' must sit between two terms, as in a = b.', t.pos);
        default: throw LogicError('Expected a formula' + where(t) + ' but found ' + describe(t) + '.', t.pos);
      }
    }
    var f = pIff();
    if (i < toks.length) {
      var t = toks[i];
      if (t.k === 'rp') throw LogicError('Unexpected closing bracket "' + t.v + '"' + where(t) + ' (there is no matching opening bracket).', t.pos);
      throw LogicError('Unexpected ' + describe(t) + where(t) + '. Is a connective missing? (Predicate arguments go directly after the letter, e.g. Fa, Rxy.)', t.pos);
    }
    return f;
  }

  /* ---------------- Printing ---------------- */
  var SYM = { and: '∧', or: '∨', imp: '→', iff: '↔' };
  function isBin(f) { return f.t === 'and' || f.t === 'or' || f.t === 'imp' || f.t === 'iff'; }
  function show(f) {
    switch (f.t) {
      case 'pred': return f.n + f.args.join('');
      case 'eq': return f.l + ' = ' + f.r;
      case 'bot': return '⊥';
      case 'not': return '¬' + (isBin(f.a) ? '(' + show(f.a) + ')' : show(f.a));
      case 'all': return '∀' + f.v + (isBin(f.a) ? '(' + show(f.a) + ')' : show(f.a));
      case 'ex': return '∃' + f.v + (isBin(f.a) ? '(' + show(f.a) + ')' : show(f.a));
      default: {
        var L = show(f.a), R = show(f.b);
        if (isBin(f.a) && !(f.a.t === f.t && (f.t === 'and' || f.t === 'or'))) L = '(' + L + ')';
        if (isBin(f.b)) R = '(' + R + ')';
        return L + ' ' + SYM[f.t] + ' ' + R;
      }
    }
  }
  function key(f) { return show(f); }
  function same(a, b) { return !!a && !!b && key(a) === key(b); }
  /* Pretty-print an ASCII/Unicode formula string; returns the input unchanged if it does not parse. */
  function pretty(s) { try { return show(parse(s)); } catch (e) { return s; } }

  /* ---------------- Syntax helpers ---------------- */
  function atoms(f, acc) {
    acc = acc || [];
    (function walk(g) {
      if (g.t === 'pred') { if (!g.args.length && acc.indexOf(g.n) < 0) acc.push(g.n); }
      else if (g.t === 'not' || g.t === 'all' || g.t === 'ex') walk(g.a);
      else if (isBin(g)) { walk(g.a); walk(g.b); }
    })(f);
    return acc;
  }
  function isPropositional(f) {
    if (f.t === 'pred') return f.args.length === 0;
    if (f.t === 'bot') return true;
    if (f.t === 'not') return isPropositional(f.a);
    if (isBin(f)) return isPropositional(f.a) && isPropositional(f.b);
    return false;
  }
  function terms(f, acc) {
    acc = acc || [];
    function add(t) { if (acc.indexOf(t) < 0) acc.push(t); }
    (function walk(g) {
      if (g.t === 'pred') g.args.forEach(add);
      else if (g.t === 'eq') { add(g.l); add(g.r); }
      else if (g.t === 'not' || g.t === 'all' || g.t === 'ex') walk(g.a);
      else if (isBin(g)) { walk(g.a); walk(g.b); }
    })(f);
    return acc;
  }
  function names(f) { return terms(f).filter(function (t) { return !isVar(t); }); }
  function freeVars(f, bound, acc) {
    bound = bound || []; acc = acc || [];
    function chk(t) { if (isVar(t) && bound.indexOf(t) < 0 && acc.indexOf(t) < 0) acc.push(t); }
    if (f.t === 'pred') f.args.forEach(chk);
    else if (f.t === 'eq') { chk(f.l); chk(f.r); }
    else if (f.t === 'not') freeVars(f.a, bound, acc);
    else if (f.t === 'all' || f.t === 'ex') freeVars(f.a, bound.concat([f.v]), acc);
    else if (isBin(f)) { freeVars(f.a, bound, acc); freeVars(f.b, bound, acc); }
    return acc;
  }
  function subst(f, x, c) {
    switch (f.t) {
      case 'pred': return { t: 'pred', n: f.n, args: f.args.map(function (a) { return a === x ? c : a; }) };
      case 'eq': return { t: 'eq', l: f.l === x ? c : f.l, r: f.r === x ? c : f.r };
      case 'bot': return f;
      case 'not': return { t: 'not', a: subst(f.a, x, c) };
      case 'all': case 'ex': return f.v === x ? f : { t: f.t, v: f.v, a: subst(f.a, x, c) };
      default: return { t: f.t, a: subst(f.a, x, c), b: subst(f.b, x, c) };
    }
  }
  function subformulas(f) {
    var out = [], seen = {};
    (function walk(g) {
      if (g.t === 'not') walk(g.a);
      else if (isBin(g)) { walk(g.a); walk(g.b); }
      if (g.t === 'pred' || g.t === 'bot') return;
      var k = key(g); if (!seen[k]) { seen[k] = 1; out.push(g); }
    })(f);
    return out;
  }
  function mainConnective(f) { return { not: '¬', and: '∧', or: '∨', imp: '→', iff: '↔', all: '∀', ex: '∃' }[f.t] || null; }

  /* ---------------- Propositional semantics ---------------- */
  function evaluate(f, v) {
    switch (f.t) {
      case 'pred': if (f.args.length) throw LogicError('Predicates need a model, not a row of a truth table.'); if (!(f.n in v)) throw LogicError('No truth value for ' + f.n); return !!v[f.n];
      case 'bot': return false;
      case 'not': return !evaluate(f.a, v);
      case 'and': return evaluate(f.a, v) && evaluate(f.b, v);
      case 'or': return evaluate(f.a, v) || evaluate(f.b, v);
      case 'imp': return !evaluate(f.a, v) || evaluate(f.b, v);
      case 'iff': return evaluate(f.a, v) === evaluate(f.b, v);
      default: throw LogicError('Quantifiers and identity cannot be evaluated by truth tables.');
    }
  }
  function sortAtoms(a) { return a.slice().sort(function (x, y) { return x.localeCompare(y, 'en', { numeric: true }); }); }
  function valuations(at) {
    var n = at.length, rows = [];
    for (var r = 0; r < (1 << n); r++) { var v = {}; for (var k = 0; k < n; k++) v[at[k]] = !((r >> (n - 1 - k)) & 1); rows.push(v); }
    return rows;
  }
  function requireProp(f, label) { if (!isPropositional(f)) throw LogicError((label || 'This formula') + ' uses quantifiers, predicates with arguments or identity; truth tables only handle propositional logic.'); }
  var MAX_ATOMS = 10;
  function truthTable(input) {
    var f = typeof input === 'string' ? parse(input) : input;
    requireProp(f);
    var at = sortAtoms(atoms(f));
    if (at.length > MAX_ATOMS) throw LogicError('Too many sentence letters (' + at.length + '); the limit is ' + MAX_ATOMS + '.');
    var cols = subformulas(f);
    var rows = valuations(at).map(function (v) { return { v: v, vals: cols.map(function (c) { return evaluate(c, v); }) }; });
    var main = rows.map(function (r) { return r.vals.length ? r.vals[r.vals.length - 1] : evaluate(f, r.v); });
    var cls = main.every(Boolean) ? 'tautology' : (main.some(Boolean) ? 'contingent' : 'contradiction');
    return { formula: f, atoms: at, columns: cols, rows: rows, main: main, classification: cls };
  }
  function classify(s) { return truthTable(s).classification; }
  function checkArgument(premises, conclusion) {
    var P = premises.map(function (p) { return typeof p === 'string' ? parse(p) : p; });
    var C = typeof conclusion === 'string' ? parse(conclusion) : conclusion;
    P.forEach(function (p, k) { requireProp(p, 'Premise ' + (k + 1)); }); requireProp(C, 'The conclusion');
    var at = []; P.forEach(function (p) { atoms(p, at); }); atoms(C, at); at = sortAtoms(at);
    if (at.length > MAX_ATOMS) throw LogicError('Too many sentence letters (' + at.length + '); the limit is ' + MAX_ATOMS + '.');
    var rows = valuations(at).map(function (v) {
      return { v: v, prem: P.map(function (p) { return evaluate(p, v); }), concl: evaluate(C, v) };
    });
    var counter = rows.filter(function (r) { return r.prem.every(Boolean) && !r.concl; });
    return { premises: P, conclusion: C, atoms: at, rows: rows, valid: counter.length === 0, counterexamples: counter };
  }
  function compare(a, b) {
    var A = typeof a === 'string' ? parse(a) : a, B = typeof b === 'string' ? parse(b) : b;
    requireProp(A, 'The first formula'); requireProp(B, 'The second formula');
    var at = sortAtoms(atoms(B, atoms(A)));
    if (at.length > MAX_ATOMS) throw LogicError('Too many sentence letters.');
    var rows = valuations(at).map(function (v) { return { v: v, a: evaluate(A, v), b: evaluate(B, v) }; });
    var aNotB = rows.filter(function (r) { return r.a && !r.b; }), bNotA = rows.filter(function (r) { return r.b && !r.a; });
    return { A: A, B: B, atoms: at, rows: rows, equivalent: !aNotB.length && !bNotA.length, aEntailsB: !aNotB.length, bEntailsA: !bNotA.length, aNotB: aNotB, bNotA: bNotA };
  }
  /* Split "P1, P2 therefore C" (or |= ⊨ ⊢ ∴) into premises and conclusion; top-level commas separate premises. */
  function splitArgument(s) {
    var m = s.split(/\s*(?:\|=|⊨|⊢|∴|\btherefore\b)\s*/);
    if (m.length > 2) throw LogicError('Use only one "therefore" sign (∴, |=, ⊢ or the word therefore).');
    if (m.length === 1) return null;
    var prem = splitTop(m[0]);
    return { premises: prem, conclusion: m[1] };
  }
  function splitTop(s) {
    var out = [], depth = 0, cur = '';
    for (var k = 0; k < s.length; k++) {
      var ch = s[k];
      if ('([{'.indexOf(ch) >= 0) depth++; else if (')]}'.indexOf(ch) >= 0) depth--;
      if (ch === ',' && depth === 0) { out.push(cur); cur = ''; } else cur += ch;
    }
    if (cur.trim() || out.length) out.push(cur);
    return out.map(function (x) { return x.trim(); }).filter(function (x) { return x.length; });
  }

  /* ---------------- First-order models ---------------- */
  /* Spec: "D = {1,2,3}; a = 1; F = {1,2}; R = {<1,2>,<2,3>}; P = T" */
  function parseModel(spec) {
    var M = { domain: [], names: {}, preds: {}, atoms: {} };
    spec.split(';').map(function (x) { return x.trim(); }).filter(Boolean).forEach(function (part) {
      var m = part.match(/^([A-Za-z][0-9']*)\s*=\s*(.*)$/);
      if (!m) throw LogicError('Cannot read model clause "' + part + '".');
      var lhs = m[1], rhs = m[2].trim();
      if (lhs === 'D') { M.domain = rhs.replace(/[{}]/g, '').split(',').map(function (x) { return x.trim(); }).filter(Boolean); return; }
      if (/^[a-z]/.test(lhs)) { M.names[lhs] = rhs; return; }
      if (rhs === 'T' || rhs === 'F') { M.atoms[lhs] = rhs === 'T'; return; }
      var inner = rhs.replace(/^\{|\}$/g, '').trim(), set = {};
      if (inner) {
        if (inner.indexOf('<') >= 0) (inner.match(/<[^>]*>/g) || []).forEach(function (t) { set[t.replace(/[<>\s]/g, '')] = 1; });
        else inner.split(',').forEach(function (x) { set[x.trim()] = 1; });
      }
      M.preds[lhs] = set;
    });
    if (!M.domain.length) throw LogicError('A model needs a non-empty domain D.');
    return M;
  }
  function evalModel(f, M, g) {
    g = g || {};
    function den(t) {
      if (t in g) return g[t];
      if (t in M.names) return M.names[t];
      throw LogicError('The term ' + t + ' has no referent in the model.');
    }
    switch (f.t) {
      case 'pred':
        if (!f.args.length) { if (f.n in M.atoms) return M.atoms[f.n]; if (f.n in M.preds) return false; throw LogicError('No value for ' + f.n); }
        return !!(M.preds[f.n] || {})[f.args.map(den).join(',')];
      case 'eq': return den(f.l) === den(f.r);
      case 'bot': return false;
      case 'not': return !evalModel(f.a, M, g);
      case 'and': return evalModel(f.a, M, g) && evalModel(f.b, M, g);
      case 'or': return evalModel(f.a, M, g) || evalModel(f.b, M, g);
      case 'imp': return !evalModel(f.a, M, g) || evalModel(f.b, M, g);
      case 'iff': return evalModel(f.a, M, g) === evalModel(f.b, M, g);
      case 'all': case 'ex': {
        var res = f.t === 'all';
        for (var k = 0; k < M.domain.length; k++) {
          var h = Object.assign({}, g); h[f.v] = M.domain[k];
          var val = evalModel(f.a, M, h);
          if (f.t === 'all' && !val) return false;
          if (f.t === 'ex' && val) return true;
        }
        return res;
      }
    }
    throw LogicError('Unknown formula type.');
  }

  /* ---------------- Proof checker ---------------- */
  var RULES = {
    'PR': [], 'AS': [], 'R': ['l'], '∧I': ['l', 'l'], '∧E': ['l'], '∨I': ['l'], '∨E': ['l', 's', 's'],
    '→I': ['s'], '→E': ['l', 'l'], '↔I': ['s', 's'], '↔E': ['l', 'l'], '¬I': ['s'], '¬E': ['l', 'l'],
    'X': ['l'], 'IP': ['s'], 'DNE': ['l'], 'TND': ['s', 's'], 'RAA': ['s'],
    'MT': ['l', 'l'], 'DS': ['l', 'l'], 'DNI': ['l'], 'HS': ['l', 'l'], 'DEM': ['l'],
    '∀E': ['l'], '∀I': ['l'], '∃I': ['l'], '∃E': ['l', 's'], '=I': [], '=E': ['l', 'l'], 'CQ': ['l']
  };
  var DERIVED = { MT: 1, DS: 1, DNI: 1, HS: 1, DEM: 1, CQ: 1, TND: 1, DNE: 1 };
  var PRED_RULES = { '∀E': 1, '∀I': 1, '∃I': 1, '∃E': 1, '=I': 1, '=E': 1, 'CQ': 1 };
  var ALIAS = {
    'P': 'PR', 'PREM': 'PR', 'PREMISE': 'PR', 'A': 'AS', 'ASS': 'AS', 'ASSUME': 'AS', 'ASSUMPTION': 'AS', 'HYP': 'AS', 'H': 'AS',
    'REIT': 'R', 'RE': 'R', 'MP': '→E', 'CP': '→I', 'EFQ': 'X', 'EXFALSO': 'X', '⊥E': 'X', '⊥I': '¬E', 'DN': 'DNE', 'LEM': 'TND',
    'DEMORGAN': 'DEM', 'QN': 'CQ', 'UI': '∀E', 'UG': '∀I', 'EG': '∃I', 'FORALLE': '∀E', 'FORALLI': '∀I', 'EXISTSE': '∃E', 'EXISTSI': '∃I', 'ID': '=I', 'LL': '=E'
  };
  function normRule(name) {
    var x = (name || '').replace(/\s+/g, '');
    x = x.replace(/<->|<=>|≡/g, '↔').replace(/->|=>|⊃/g, '→').replace(/[&^]/g, '∧').replace(/_\|_|#/g, '⊥');
    x = x.replace(/^[~!−-](?=[IiEe]$)/, '¬').replace(/^[vV|](?=[IiEe]$)/, '∨');
    x = x.toUpperCase();
    if (ALIAS[x]) x = ALIAS[x];
    return x;
  }
  function parseJust(s) {
    s = (s || '').trim();
    var m = s.match(/^([^0-9]*?)\s*([0-9][\s\S]*)?$/);
    var name = m ? m[1].replace(/[,:]\s*$/, '').trim() : s, refsTxt = m && m[2] ? m[2] : '';
    var rule = normRule(name), refs = [], bad = null;
    refsTxt.replace(/\s*[-–—]\s*/g, '-').split(/[,;\s]+/).filter(Boolean).forEach(function (r) {
      var a;
      if ((a = r.match(/^(\d+)-(\d+)$/))) refs.push({ k: 's', i: +a[1], j: +a[2] });
      else if ((a = r.match(/^(\d+)$/))) refs.push({ k: 'l', n: +a[1] });
      else bad = r;
    });
    return { raw: s, name: name, rule: rule, refs: refs, bad: bad };
  }
  function ruleLabel(r) { return r; }

  function deMorganForms(f) {
    var out = [];
    if (f.t === 'not' && f.a.t === 'or') out.push({ t: 'and', a: { t: 'not', a: f.a.a }, b: { t: 'not', a: f.a.b } });
    if (f.t === 'not' && f.a.t === 'and') out.push({ t: 'or', a: { t: 'not', a: f.a.a }, b: { t: 'not', a: f.a.b } });
    if (f.t === 'and' && f.a.t === 'not' && f.b.t === 'not') out.push({ t: 'not', a: { t: 'or', a: f.a.a, b: f.b.a } });
    if (f.t === 'or' && f.a.t === 'not' && f.b.t === 'not') out.push({ t: 'not', a: { t: 'and', a: f.a.a, b: f.b.a } });
    return out;
  }
  function cqForms(f) {
    var out = [];
    if (f.t === 'not' && f.a.t === 'all') out.push({ t: 'ex', v: f.a.v, a: { t: 'not', a: f.a.a } });
    if (f.t === 'not' && f.a.t === 'ex') out.push({ t: 'all', v: f.a.v, a: { t: 'not', a: f.a.a } });
    if (f.t === 'ex' && f.a.t === 'not') out.push({ t: 'not', a: { t: 'all', v: f.v, a: f.a.a } });
    if (f.t === 'all' && f.a.t === 'not') out.push({ t: 'not', a: { t: 'ex', v: f.v, a: f.a.a } });
    return out;
  }
  function sameMod(p, q, a, b) {
    function tq(s, t) { return s === t || (s === a && t === b) || (s === b && t === a); }
    if (p.t !== q.t) return false;
    switch (p.t) {
      case 'pred': return p.n === q.n && p.args.length === q.args.length && p.args.every(function (x, k) { return tq(x, q.args[k]); });
      case 'eq': return tq(p.l, q.l) && tq(p.r, q.r);
      case 'bot': return true;
      case 'not': return sameMod(p.a, q.a, a, b);
      case 'all': case 'ex': return p.v === q.v && sameMod(p.a, q.a, a, b);
      default: return sameMod(p.a, q.a, a, b) && sameMod(p.b, q.b, a, b);
    }
  }

  /* lines: [{f: 'P → Q', j: 'PR', d: 0}, ...]  d = subproof depth (0 = main proof).
     opts: {premises: [...], conclusion: '...', allowDerived: true, allowPredicate: true}
     Returns {lines:[{ok, msg, formula, rule}], ok, complete, summary} */
  function checkProof(lines, opts) {
    opts = opts || {};
    var allowDerived = opts.allowDerived !== false, allowPred = opts.allowPredicate !== false;
    var N = lines.length, res = [], F = [], J = [], ctx = [], subs = [], stack = [], seenNonPremise = false;
    for (var k = 0; k < N; k++) res.push({ ok: true, msg: '', formula: null, rule: null });
    function fail(k, m) { if (res[k].ok) { res[k].ok = false; res[k].msg = m; } }
    // Pass 1: formulas, justifications, structure
    for (k = 0; k < N; k++) {
      var ln = lines[k], d = Math.max(0, ln.d | 0);
      try { F[k] = parse(String(ln.f || '')); res[k].formula = show(F[k]); }
      catch (e) { F[k] = null; fail(k, 'Formula: ' + e.message); }
      if (F[k]) { var fv = freeVars(F[k]); if (fv.length) fail(k, 'The formula contains the free variable ' + fv.join(', ') + ', so it is not a sentence. Every variable must be bound by a quantifier.'); }
      var j = J[k] = parseJust(ln.j); res[k].rule = j.rule;
      if (!j.raw) fail(k, 'Missing justification. Write a rule and line numbers, e.g. "→E 1, 2", or PR / AS.');
      else if (j.bad) fail(k, 'Cannot read the line reference "' + j.bad + '". Use numbers like 3 or ranges like 2-5, separated by commas.');
      else if (!RULES.hasOwnProperty(j.rule)) fail(k, 'Unknown rule "' + j.name + '". See the list of rules on this page.');
      else if (!allowDerived && DERIVED[j.rule]) fail(k, j.rule + ' is a derived rule, which this exercise does not allow. Use only the basic rules.');
      else if (!allowPred && PRED_RULES[j.rule]) fail(k, j.rule + ' is a predicate-logic rule, which is not available here.');
      if (j.rule === 'PR') {
        if (d !== 0) fail(k, 'Premises belong to the main proof (depth 0), not inside a subproof.');
        if (seenNonPremise) fail(k, 'Premises must all come at the very start of the proof.');
        stack = [];
      } else if (j.rule === 'AS') {
        seenNonPremise = true;
        if (d < 1) { fail(k, 'An assumption must open a new subproof: indent it (depth 1 or more).'); d = 1; }
        if (d > stack.length + 1) { fail(k, 'This assumption is indented ' + (d - stack.length - 1) + ' level(s) too far: a new subproof can only be one level deeper than the line before it.'); d = stack.length + 1; }
        stack = stack.slice(0, d - 1);
        var s = { id: subs.length, start: k, end: k, depth: d, parent: stack.slice() };
        subs.push(s); stack.push(s.id);
      } else {
        seenNonPremise = true;
        if (d > stack.length) { fail(k, 'This line is at depth ' + d + ' but there is no open subproof at that depth. Only an assumption (AS) can open a subproof.'); d = stack.length; }
        stack = stack.slice(0, d);
      }
      ctx[k] = stack.slice();
      ctx[k].forEach(function (id) { subs[id].end = k; });
    }
    function isPrefix(a, b) { if (a.length > b.length) return false; for (var q = 0; q < a.length; q++) if (a[q] !== b[q]) return false; return true; }
    function lineRef(k, n) { // returns formula or throws message
      var m = n - 1;
      if (m < 0 || m >= N) throw 'There is no line ' + n + '.';
      if (m >= k) throw 'Line ' + n + ' comes at or after this line; you can only cite earlier lines.';
      if (!isPrefix(ctx[m], ctx[k])) throw 'Line ' + n + ' is not available here: it lies inside a subproof that has already been closed.';
      if (!F[m]) throw 'Line ' + n + ' does not contain a well-formed formula.';
      return F[m];
    }
    function subRef(k, i, jj) { // returns {first, last, sub}
      var a = i - 1, b = jj - 1;
      if (a < 0 || b >= N || a > b) throw 'The range ' + i + '–' + jj + ' does not make sense.';
      if (b >= k) throw 'The subproof ' + i + '–' + jj + ' must be finished before this line.';
      var sub = null;
      for (var q = 0; q < subs.length; q++) if (subs[q].start === a) sub = subs[q];
      if (!sub) throw 'Line ' + i + ' does not begin a subproof: a subproof must begin with an assumption (AS).';
      if (ctx[b][ctx[b].length - 1] !== sub.id || sub.end !== b) throw 'Line ' + jj + ' is not the last line of the subproof that begins on line ' + i + ' (it ends on line ' + (sub.end + 1) + ').';
      if (ctx[k].indexOf(sub.id) >= 0) throw 'You are still inside the subproof ' + i + '–' + jj + '. Close it (reduce the indentation) before using it.';
      if (!isPrefix(sub.parent, ctx[k])) throw 'The subproof ' + i + '–' + jj + ' is not available here: it lies inside another subproof that has already been closed.';
      if (!F[a] || !F[b]) throw 'The subproof ' + i + '–' + jj + ' contains a malformed formula.';
      return { first: F[a], last: F[b], sub: sub };
    }
    function openAssumptions(k) { // premises + assumptions of subproofs open at line k
      var out = [];
      for (var q = 0; q < N; q++) if (J[q].rule === 'PR' && F[q]) out.push({ n: q + 1, f: F[q] });
      ctx[k].forEach(function (id) { var st = subs[id].start; if (F[st]) out.push({ n: st + 1, f: F[st] }); });
      return out;
    }
    var S = show;
    function checkRule(k) {
      var j = J[k], f = F[k], spec = RULES[j.rule], refs = j.refs, r = j.rule;
      if (spec.length !== refs.length || spec.some(function (t, q) { return refs[q].k !== t; })) {
        var want = spec.map(function (t) { return t === 'l' ? 'a line number' : 'a subproof range like 3-5'; });
        if (r === 'PR' || r === 'AS' || r === '=I') return r + ' does not cite any lines.';
        return r + ' cites ' + want.join(', then ') + '.' + (r === '∨E' ? ' Example: ∨E 1, 2-4, 5-7.' : r === '∃E' ? ' Example: ∃E 1, 2-5.' : '');
      }
      var L = [], Sb = [];
      refs.forEach(function (x) { if (x.k === 'l') L.push(lineRef(k, x.n)); else Sb.push(subRef(k, x.i, x.j)); });
      var A, B, x;
      function two(test) { return test(L[0], L[1]) || test(L[1], L[0]); }
      switch (r) {
        case 'PR':
          if (opts.premises && opts.premises.length) {
            var ok = opts.premises.some(function (p) { try { return same(parse(p), f); } catch (e) { return false; } });
            if (!ok) return 'This is not one of the premises of the argument you are proving.';
          }
          return null;
        case 'AS': return null;
        case 'R': return same(L[0], f) ? null : 'Reiteration must copy line ' + refs[0].n + ' exactly (' + S(L[0]) + ').';
        case '∧I':
          if (f.t !== 'and') return '∧I must produce a conjunction (A ∧ B).';
          return two(function (a, b) { return same(a, f.a) && same(b, f.b); }) ? null : '∧I: the cited lines must be the two conjuncts, ' + S(f.a) + ' and ' + S(f.b) + '.';
        case '∧E':
          if (L[0].t !== 'and') return '∧E needs a conjunction on line ' + refs[0].n + ', but its main connective is ' + (mainConnective(L[0]) || 'none') + '.';
          return same(L[0].a, f) || same(L[0].b, f) ? null : '∧E: this line must be one of the conjuncts of line ' + refs[0].n + ' (' + S(L[0].a) + ' or ' + S(L[0].b) + ').';
        case '∨I':
          if (f.t !== 'or') return '∨I must produce a disjunction (A ∨ B).';
          return same(f.a, L[0]) || same(f.b, L[0]) ? null : '∨I: line ' + refs[0].n + ' (' + S(L[0]) + ') must be one of the disjuncts of this line.';
        case '∨E': {
          if (L[0].t !== 'or') return '∨E needs a disjunction on line ' + refs[0].n + '.';
          var s1 = Sb[0], s2 = Sb[1];
          var fits = function (p, q) { return same(p.first, L[0].a) && same(q.first, L[0].b); };
          if (!fits(s1, s2) && !fits(s2, s1)) return '∨E: one subproof must assume ' + S(L[0].a) + ' and the other ' + S(L[0].b) + '.';
          if (!same(s1.last, f) || !same(s2.last, f)) return '∨E: both subproofs must end with this line\'s formula, ' + S(f) + '.';
          return null;
        }
        case '→I':
          if (f.t !== 'imp') return '→I must produce a conditional (A → B).';
          if (!same(Sb[0].first, f.a)) return '→I: the subproof must assume the antecedent, ' + S(f.a) + '.';
          if (!same(Sb[0].last, f.b)) return '→I: the subproof must end with the consequent, ' + S(f.b) + '.';
          return null;
        case '→E':
          return two(function (c, a) { return c.t === 'imp' && same(c.a, a) && same(c.b, f); }) ? null : '→E (modus ponens) needs a conditional A → B and its antecedent A; this line must then be B.';
        case '↔I': {
          if (f.t !== 'iff') return '↔I must produce a biconditional (A ↔ B).';
          var p = Sb[0], q = Sb[1];
          var g = function (u, w) { return same(u.first, f.a) && same(u.last, f.b) && same(w.first, f.b) && same(w.last, f.a); };
          return g(p, q) || g(q, p) ? null : '↔I needs one subproof from ' + S(f.a) + ' to ' + S(f.b) + ' and another from ' + S(f.b) + ' to ' + S(f.a) + '.';
        }
        case '↔E':
          return two(function (c, a) { return c.t === 'iff' && ((same(c.a, a) && same(c.b, f)) || (same(c.b, a) && same(c.a, f))); }) ? null : '↔E needs a biconditional A ↔ B and one side of it; this line must be the other side.';
        case '¬I':
          if (f.t !== 'not') return '¬I must produce a negation ¬A.';
          if (!same(Sb[0].first, f.a)) return '¬I: the subproof must assume ' + S(f.a) + '.';
          if (Sb[0].last.t !== 'bot') return '¬I: the subproof must end with ⊥.';
          return null;
        case '¬E':
          if (f.t !== 'bot') return '¬E produces ⊥ (a contradiction) from A and ¬A.';
          return two(function (n, a) { return n.t === 'not' && same(n.a, a); }) ? null : '¬E: the cited lines must be some formula A and its negation ¬A.';
        case 'X': return L[0].t === 'bot' ? null : 'X (ex falso) needs ⊥ on the cited line.';
        case 'IP':
          if (!same(Sb[0].first, { t: 'not', a: f })) return 'IP: the subproof must assume ' + S({ t: 'not', a: f }) + ' (the negation of this line).';
          if (Sb[0].last.t !== 'bot') return 'IP: the subproof must end with ⊥.';
          return null;
        case 'RAA': {
          if (Sb[0].last.t !== 'bot') return 'RAA: the subproof must end with ⊥.';
          if (f.t === 'not' && same(Sb[0].first, f.a)) return null;
          if (same(Sb[0].first, { t: 'not', a: f })) return null;
          return 'RAA: assume A and derive ⊥ to conclude ¬A, or assume ¬A and derive ⊥ to conclude A.';
        }
        case 'DNE': return L[0].t === 'not' && L[0].a.t === 'not' && same(L[0].a.a, f) ? null : 'DNE: the cited line must be ¬¬A, and this line A.';
        case 'DNI': return f.t === 'not' && f.a.t === 'not' && same(f.a.a, L[0]) ? null : 'DNI: from A infer ¬¬A.';
        case 'TND': {
          var a1 = Sb[0], a2 = Sb[1];
          var h = function (u, w) { return same(w.first, { t: 'not', a: u.first }); };
          if (!h(a1, a2) && !h(a2, a1)) return 'TND: one subproof must assume A and the other ¬A.';
          return same(a1.last, f) && same(a2.last, f) ? null : 'TND: both subproofs must end with this line\'s formula.';
        }
        case 'MT':
          return two(function (c, n) { return c.t === 'imp' && n.t === 'not' && same(c.b, n.a) && same(f, { t: 'not', a: c.a }); }) ? null : 'MT (modus tollens): from A → B and ¬B infer ¬A.';
        case 'DS':
          return two(function (d, n) { return d.t === 'or' && n.t === 'not' && ((same(d.a, n.a) && same(d.b, f)) || (same(d.b, n.a) && same(d.a, f))); }) ? null : 'DS (disjunctive syllogism): from A ∨ B and ¬A infer B (or from ¬B infer A).';
        case 'HS':
          return two(function (c1, c2) { return c1.t === 'imp' && c2.t === 'imp' && same(c1.b, c2.a) && f.t === 'imp' && same(f.a, c1.a) && same(f.b, c2.b); }) ? null : 'HS (hypothetical syllogism): from A → B and B → C infer A → C.';
        case 'DEM':
          return deMorganForms(L[0]).some(function (g) { return same(g, f); }) ? null : 'DeM: the line must be the De Morgan transform of line ' + refs[0].n + ' (¬(A ∨ B) ⇔ ¬A ∧ ¬B, ¬(A ∧ B) ⇔ ¬A ∨ ¬B).';
        case 'CQ':
          return cqForms(L[0]).some(function (g) { return same(g, f); }) ? null : 'CQ: ¬∀xA ⇔ ∃x¬A and ¬∃xA ⇔ ∀x¬A.';
        case '∀E': {
          if (L[0].t !== 'all') return '∀E needs a universally quantified sentence ∀x A on line ' + refs[0].n + '.';
          A = L[0].a; x = L[0].v;
          if (same(A, f) && freeVars(A).indexOf(x) < 0) return null;
          var cands = terms(f);
          return cands.some(function (c) { return !isVar(c) && same(subst(A, x, c), f); }) ? null : '∀E: this line must be ' + S(A) + ' with every free ' + x + ' replaced by one and the same name.';
        }
        case '∃I': {
          if (f.t !== 'ex') return '∃I must produce an existentially quantified sentence ∃x A.';
          A = f.a; x = f.v;
          if (same(A, L[0])) return null;
          return terms(L[0]).some(function (c) { return !isVar(c) && same(subst(A, x, c), L[0]); }) ? null : '∃I: line ' + refs[0].n + ' must be ' + S(A) + ' with ' + x + ' replaced by a name.';
        }
        case '∀I': {
          if (f.t !== 'all') return '∀I must produce a universally quantified sentence ∀x A.';
          A = f.a; x = f.v;
          var fnames = names(f), found = null, why = null;
          names(L[0]).concat(['__none__']).forEach(function (c) {
            if (found) return;
            var inst = c === '__none__' ? A : subst(A, x, c);
            if (c !== '__none__' && fnames.indexOf(c) >= 0) return;
            if (!same(inst, L[0])) return;
            if (c === '__none__') { found = c; return; }
            var bad = openAssumptions(k).filter(function (o) { return names(o.f).indexOf(c) >= 0; });
            if (bad.length) { why = '∀I: the name ' + c + ' occurs in an undischarged assumption or premise (line ' + bad[0].n + '), so it is not arbitrary.'; return; }
            found = c;
          });
          if (found) return null;
          return why || '∀I: line ' + refs[0].n + ' must be ' + S(A) + ' with ' + x + ' replaced by a name that does not occur in ' + S(f) + '.';
        }
        case '∃E': {
          if (L[0].t !== 'ex') return '∃E needs an existentially quantified sentence ∃x A on line ' + refs[0].n + '.';
          A = L[0].a; x = L[0].v;
          var sb = Sb[0], why2 = null, okE = false;
          if (!same(sb.last, f)) return '∃E: the subproof must end with this line\'s formula, ' + S(f) + '.';
          names(sb.first).forEach(function (c) {
            if (okE) return;
            if (!same(subst(A, x, c), sb.first)) return;
            if (names(L[0]).indexOf(c) >= 0) { why2 = '∃E: the name ' + c + ' already occurs in ' + S(L[0]) + '.'; return; }
            if (names(f).indexOf(c) >= 0) { why2 = '∃E: the name ' + c + ' must not occur in the conclusion ' + S(f) + '.'; return; }
            var bad = openAssumptions(k).filter(function (o) { return names(o.f).indexOf(c) >= 0; });
            if (bad.length) { why2 = '∃E: the name ' + c + ' occurs in an undischarged assumption or premise (line ' + bad[0].n + ').'; return; }
            okE = true;
          });
          if (okE) return null;
          return why2 || '∃E: the subproof must assume ' + S(A) + ' with ' + x + ' replaced by a new name.';
        }
        case '=I': return f.t === 'eq' && f.l === f.r ? null : '=I lets you write c = c for any name c.';
        case '=E':
          return two(function (e, p) { return e.t === 'eq' && sameMod(p, f, e.l, e.r); }) ? null : '=E: from a = b and a sentence A, infer A with some occurrences of a replaced by b (or of b by a).';
      }
      return 'Unknown rule.';
    }
    for (k = 0; k < N; k++) {
      if (!res[k].ok || !F[k]) continue;
      try { var e = checkRule(k); if (e) fail(k, e); }
      catch (msg) { fail(k, typeof msg === 'string' ? msg : String(msg.message || msg)); }
    }
    var allOk = res.every(function (r) { return r.ok; });
    var last = N - 1, complete = false, summary = '';
    var concl = null;
    if (opts.conclusion) { try { concl = parse(opts.conclusion); } catch (e2) { concl = null; } }
    if (!N) summary = 'The proof is empty.';
    else if (!allOk) summary = res.filter(function (r) { return !r.ok; }).length + ' line(s) have problems.';
    else if (ctx[last].length) summary = 'Every line is correct, but the proof ends inside an open subproof. The conclusion must be at depth 0.';
    else if (concl && !same(F[last], concl)) summary = 'Every line is correct, but the last line is not the goal ' + show(concl) + '.';
    else { complete = true; summary = concl ? 'Proof complete: every line is correct and the goal ' + show(concl) + ' is reached at depth 0.' : 'Every line is correct and the proof ends at depth 0.'; }
    return { lines: res, ok: allOk, complete: complete, summary: summary, depthCtx: ctx };
  }

  /* Parse a plain-text proof: each line "| | formula ; JUST" where the number of leading bars is the depth. */
  function parseProofText(txt) {
    return txt.split('\n').map(function (l) { return l.replace(/\s+$/, ''); }).filter(function (l) { return l.trim() && !/^\s*%/.test(l); }).map(function (l) {
      var m = l.match(/^\s*((?:\|\s*)*)(.*)$/), d = (m[1].match(/\|/g) || []).length, body = m[2];
      var semi = body.lastIndexOf(';');
      return { d: d, f: semi >= 0 ? body.slice(0, semi).trim() : body.trim(), j: semi >= 0 ? body.slice(semi + 1).trim() : '' };
    });
  }
  function prettyJust(j) {
    var p = parseJust(j);
    var nm = RULES.hasOwnProperty(p.rule) ? p.rule : p.name;
    if (nm === 'DEM') nm = 'DeM';
    var refs = p.refs.map(function (r) { return r.k === 'l' ? String(r.n) : r.i + '–' + r.j; }).join(', ');
    return (nm + (refs ? ' ' + refs : '')).trim();
  }

  var api = {
    LogicError: LogicError, lex: lex, parse: parse, show: show, pretty: pretty, key: key, same: same, isVar: isVar,
    atoms: atoms, terms: terms, names: names, freeVars: freeVars, subst: subst, subformulas: subformulas, isPropositional: isPropositional,
    evaluate: evaluate, truthTable: truthTable, classify: classify, checkArgument: checkArgument, compare: compare,
    splitArgument: splitArgument, splitTop: splitTop, parseModel: parseModel, evalModel: evalModel,
    mainConnective: mainConnective, RULES: RULES, parseJust: parseJust, normRule: normRule, checkProof: checkProof, parseProofText: parseProofText, prettyJust: prettyJust, ruleLabel: ruleLabel
  };
  if (typeof module !== 'undefined' && module.exports) module.exports = api; else root.Logic = api;
})(typeof window !== 'undefined' ? window : this);
