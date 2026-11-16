// parse.js — a fast, dependency-free Markdown renderer.
//
// An original implementation of the CommonMark + GFM behaviour that
// marked 18.1.3 produces with its defaults (gfm on, breaks off, pedantic
// off, async off). Written from scratch for speed: the block layer walks
// the source with sticky regexes at a moving offset (no per-token
// substring copies), inline rendering writes straight into the output
// array in a second pass (after all link-reference definitions have been
// collected, so a definition later in the document still resolves an
// earlier paragraph), and the plain-text fast path is a hand-written
// character scanner instead of one giant regex.
//
// Public surface: parse(markdown) -> HTML string, byte-identical to
// marked.parse(markdown) with default options.

// ------------------------------------------------------------------
// Small string helpers
// ------------------------------------------------------------------

const ESCAPES = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };
const escapeChar = (ch) => ESCAPES[ch];

// Escape HTML special characters. With `encode`, every & < > " ' is
// escaped; without it, an & that already begins a character reference
// or a named entity is left alone (named entities pass through).
const ESC_TEST = /[&<>"']/;
const ESC_REPLACE = /[&<>"']/g;
const ESC_TEST_NO_ENCODE = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/;
const ESC_REPLACE_NO_ENCODE = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;
function escHtml(str, encode) {
  if (encode) {
    return ESC_TEST.test(str) ? str.replace(ESC_REPLACE, escapeChar) : str;
  }
  return ESC_TEST_NO_ENCODE.test(str) ? str.replace(ESC_REPLACE_NO_ENCODE, escapeChar) : str;
}

// Decode numeric character references (&#169; &#xA9;) and turn a bare &
// (one that does not start a valid reference) into &amp;. Named entities
// such as &copy; are intentionally left untouched here.
const NUM_REF = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));/;
const NUM_REF_OR_AMP = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;
function unescapeEntities(str) {
  if (!NUM_REF.test(str)) return str;
  return str.replace(NUM_REF_OR_AMP, (whole, dec, hex) => {
    if (dec === undefined && hex === undefined) return '&amp;';
    const cp = dec === undefined ? parseInt(hex, 16) : parseInt(dec, 10);
    if (cp === 0 || cp > 0x10ffff || (cp >= 0xd800 && cp <= 0xdfff)) return '\uFFFD';
    if (cp === 38) return '&amp;';
    return String.fromCodePoint(cp);
  });
}

// Sanitize a link destination the way a browser would: encodeURI, but
// keep literal % characters (so %25 stays %25, not %2525). Returns null
// when the destination cannot be encoded.
const PERCENT = /%25/g;
function cleanUrl(href) {
  try {
    return encodeURI(href).replace(PERCENT, '%');
  } catch {
    return null;
  }
}

// Split a table row on unescaped pipes, trim cells, and pad/truncate to
// the header width. A \| inside a cell is a literal pipe.
const FIND_PIPE = /\|/g;
const SPLIT_PIPE = / \|/;
const SLASH_PIPE = /\\\|/g;
function splitCells(row, count) {
  const marked = row.replace(FIND_PIPE, (ch, off, s) => {
    let escaped = false;
    let p = off;
    for (; --p >= 0 && s[p] === '\\';) escaped = !escaped;
    return escaped ? '|' : ' |';
  });
  const cells = marked.split(SPLIT_PIPE);
  let i = 0;
  if (!cells[0].trim()) cells.shift();
  if (cells.length > 0 && !cells.at(-1)?.trim()) cells.pop();
  if (count) {
    if (cells.length > count) cells.splice(count);
    else for (; cells.length < count;) cells.push('');
  }
  for (; i < cells.length; i++) cells[i] = cells[i].trim().replace(SLASH_PIPE, '|');
  return cells;
}

// Remove `ch` characters from the end of a string. When `all` is set,
// also strip any other character (used to trim trailing newlines while
// keeping a count of what was removed).
function rtrim(str, ch, all) {
  const n = str.length;
  if (n === 0) return '';
  let s = 0;
  for (; s < n;) {
    const c = str.charAt(n - s - 1);
    if (c === ch && !all) s++;
    else if (c !== ch && all) s++;
    else break;
  }
  return str.slice(0, n - s);
}

// Drop trailing blank lines from a block of text, but keep the text
// untouched when there are at most two trailing lines to drop (the
// common case of a block ending with a single blank line).
const BLANK_LINE = /^[ \t]*$/;
function trimBlankTail(text) {
  const lines = text.split('\n');
  let t = lines.length - 1;
  for (; t >= 0 && BLANK_LINE.test(lines[t]);) t--;
  return lines.length - t <= 2 ? text : lines.slice(0, t + 1).join('\n');
}

// Normalize a link label for lookup: trim, collapse inner whitespace
// to single spaces, and case-fold (with the toUpperCase round-trip
// that makes the fold locale-independent for odd characters).
const MULTI_SPACE = /\s+/g;
function normalizeLabel(label) {
  return label.trim().replace(MULTI_SPACE, ' ').toLowerCase().toUpperCase().toLowerCase();
}

// Find the index of an unmatched close character in `str`, tracking
// the open/close pair given by `pair` (two characters, e.g. "()").
// Backslash escapes are skipped. Returns -1 when balanced or absent,
// -2 when an opener is left unclosed, otherwise the index of the
// unmatched closer.
function findUnbalanced(str, pair) {
  if (str.indexOf(pair[0]) === -1 && str.indexOf(pair[1]) === -1) return -1;
  let depth = 0;
  for (let n = 0; n < str.length; n++) {
    if (str[n] === '\\') n++;
    else if (str[n] === pair[0]) depth++;
    else if (str[n] === pair[1]) {
      depth--;
      if (depth < 0) return n;
    }
  }
  return depth > 0 ? -2 : -1;
}

// Expand tabs to spaces the way a 4-space tab stop does: a tab advances
// to the next multiple of 4 columns (counting from `startCol`).
function expandTabs(str, startCol = 0) {
  let col = startCol;
  let out = '';
  for (const ch of str) {
    if (ch === '\t') {
      const w = 4 - (col % 4);
      out += ' '.repeat(w);
      col += w;
    } else {
      out += ch;
      col++;
    }
  }
  return out;
}

// Length of a string in Unicode code points (astral characters count
// once), without building an intermediate array.
function codePointLen(str) {
  let n = 0;
  for (const _ch of str) n++;
  return n;
}

// Last code point of a string, or '' when empty.
function lastCodePoint(str) {
  if (!str) return '';
  let last = '';
  for (const ch of str) last = ch;
  return last;
}

// First code point of a string, as a string.
function firstCodePoint(str) {
  for (const ch of str) return ch;
  return '';
}

// ------------------------------------------------------------------
// Character-code lookup tables (Uint8Array indexed by char code).
// ASCII only; anything >= 128 reads as 0 and falls through to the
// slow path, which is correct because all of these classes are ASCII.
// ------------------------------------------------------------------
function makeTable(chars) {
  const t = new Uint8Array(128);
  for (const c of chars) t[c.charCodeAt(0)] = 1;
  return t;
}
// Characters that may start an e-mail local part (and may appear in it).
const EMAIL_CHARS = makeTable("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789.!#$%&'*+/=?^_`{|}~-");
// Characters that end a plain-text run (the inline text scanner stops
// before any of these so the matching tokenizer gets its chance).
const TEXT_STOP = makeTable('\\<![]`*~_');
// Word characters, for the \b_ word-boundary check.
const WORD_CHARS = makeTable('abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_');
// ASCII alphanumerics.
const ALNUM = makeTable('abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789');
// ASCII punctuation / symbols (Unicode \p{P} and \p{S} restricted to ASCII).
const ASCII_PUNCT = makeTable('!"#$%&\'()*+,-./:;<=>?@[\\]^_`{|}~');
function isEmailCharCode(code) { return code < 128 && EMAIL_CHARS[code] === 1; }
function isWordCode(code) { return code < 128 && WORD_CHARS[code] === 1; }
function isAlnumCode(code) { return code < 128 && ALNUM[code] === 1; }

// ------------------------------------------------------------------
// Pattern composer and the block grammar
//
// Patterns are assembled from small fragments the same way a grammar
// is: a fragment is spliced into a template, and any ^ anchor the
// fragment carried is dropped (inside a lookahead an anchor would only
// ever match at position 0, which is never what a lookahead means).
// ------------------------------------------------------------------
const CARET_IN_FRAGMENT = /(^|[^\[])\^/g;
function compose(pattern, flags = '') {
  let src = typeof pattern === 'string' ? pattern : pattern.source;
  const api = {
    replace(from, frag) {
      let ins = typeof frag === 'string' ? frag : frag.source;
      ins = ins.replace(CARET_IN_FRAGMENT, '$1');
      src = src.replace(from, ins);
      return api;
    },
    getRegex() { return new RegExp(src, flags); },
  };
  return api;
}

// Memoized builder for the small family of indent-dependent patterns:
// the indent is clamped to 0..3, so at most four variants ever exist.
function memo4(build) {
  const cache = [];
  return (n) => {
    const k = Math.max(0, Math.min(3, n - 1));
    return cache[k] || (cache[k] = build(k));
  };
}

// Block-level HTML tags that may open a raw HTML block.
const BLOCK_TAGS = 'address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul';

// Frequently used fragments.
const RX = {
  codeRemoveIndent: /^(?: {0,3}\t| {1,4})/gm,
  outputLinkReplace: /\\([\[\]])/g,
  indentCodeCompensation: /^(\s+)(?:```)/,
  beginningSpace: /^\s+/,
  endingHash: /#$/,
  startingSpaceChar: /^ /,
  endingSpaceChar: / $/,
  endingSpaceTabChar: /[ \t]$/,
  nonSpaceChar: /[^ ]/,
  newLineCharGlobal: /\n/g,
  tabCharGlobal: /\t/g,
  leadingSpaceTab: /^[ \t]+/,
  multipleSpaceGlobal: /\s+/g,
  blankLine: /^[ \t]*$/,
  doubleBlankLine: /\n[ \t]*\n[ \t]*$/,
  blockquoteStart: /^ {0,3}>/,
  blockquoteSetextReplace: /\n {0,3}((?:=+|-+)[ \t]*)(?=\n|$)/g,
  blockquoteSetextReplace2: /^ {0,3}>[ \t]?/gm,
  blockquoteMarkerWhitespace: /^( {0,3}>)([ \t]+)/gm,
  listReplaceNesting: /^ {1,4}(?=( {4})*[^ ])/g,
  listIsTask: /^\[[ xX]\][ \t]+\S/,
  listReplaceTask: /^\[[ xX]\][ \t]+/,
  listTaskCheckbox: /\[[ xX]\]/,
  anyLine: /\n.*\n/,
  hrefBrackets: /^<(.*)>$/,
  tableDelimiter: /[:|]/,
  tableAlignChars: /^\||\| *$/g,
  tableRowBlankLine: /\n[ \t]*$/,
  tableAlignRight: /^ *-+: *$/,
  tableAlignCenter: /^ *:-+: *$/,
  tableAlignLeft: /^ *:-+ *$/,
  startATag: /^<a /i,
  endATag: /^<\/a>/i,
  startPreScriptTag: /^<(pre|code|kbd|script)(\s|>)/i,
  endPreScriptTag: /^<\/(pre|code|kbd|script)(\s|>)/i,
  startAngleBracket: /^</,
  endAngleBracket: />$/,
  unicodeAlphaNumeric: /[\p{L}\p{N}]/u,
  percentDecode: /%25/g,
  findPipe: /\|/g,
  splitPipe: / \|/,
  slashPipe: /\\\|/g,
  carriageReturn: /\r\n|\r/g,
  spaceLine: /^ +$/gm,
  notSpaceStart: /^\S*/,
  endingNewline: /\n$/,
  listItemRegex: (bull) => new RegExp(`^( {0,3}${bull})((?:[\t ][^\n]*)?(?:\n|$))`),
  nextBulletRegex: memo4((n) => new RegExp(`^ {0,${n}}(?:[*+-]|\\d{1,9}[.)])((?:[ \t][^\n]*)?(?:\\n|$))`)),
  hrRegex: memo4((n) => new RegExp(`^ {0,${n}}((?:-[ \t]*){3,}|(?:_[ \t]*){3,}|(?:\\*[ \t]*){3,})(?:\\n+|$)`)),
  fencesBeginRegex: memo4((n) => new RegExp(`^ {0,${n}}(?:\`\`\`|~~~)`)),
  headingBeginRegex: memo4((n) => new RegExp(`^ {0,${n}}#{1,6}(?:\\s|$)`)),
  htmlBeginRegex: memo4((n) => new RegExp(`^ {0,${n}}(?:</?(?:${BLOCK_TAGS})(?: +|$|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)`, 'i')),
  blockquoteBeginRegex: memo4((n) => new RegExp(`^ {0,${n}}>`)),
};

// --- Block grammar (GFM) -------------------------------------------
const BLOCK_NEWLINE = /^(?:[ \t]*(?:\n|$))+/;
const BLOCK_CODE = /^((?: {4}| {0,3}\t)[^\n]+(?:\n(?:[ \t]*(?:\n|$))*)?)+/;
const BLOCK_FENCES = /^ {0,3}(`{3,}(?=[^`\n]*(?:\n|$))|~{3,})([^\n]*)(?:\n|$)(?:|([\s\S]*?)(?:\n|$))(?: {0,3}(?:(?=`)\1`*|(?=~)\1~*) *(?=\n|$)|$)/;
const BLOCK_HR = /^ {0,3}((?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)/;
const BLOCK_HEADING = /^ {0,3}(#{1,6})(?=\s|$)(.*)(?:\n+|$)/;
const BLOCK_BULLET = / {0,3}(?:[*+-]|\d{1,9}[.)])/;
const BLOCK_LHEADING_SRC = /^(?!bull |blockCode|fences|blockquote|heading|html|table)((?:.|\n(?!\s*?\n|bull |fences|blockquote|heading|hr|html|table))+?)\n {0,3}(=+|-+)[ \t]*(?:\n+|$)/;
const BLOCK_LHEADING_GFM = compose(BLOCK_LHEADING_SRC)
  .replace(/bull/g, BLOCK_BULLET)
  .replace(/blockCode/g, /(?: {4}| {0,3}\t)/)
  .replace(/fences/g, / {0,3}(?:`{3,}|~{3,})/)
  .replace(/blockquote/g, / {0,3}>/)
  .replace(/heading/g, / {0,3}#{1,6}(?:\s|$)/)
  .replace(/hr/g, / {0,3}(?:(?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)/)
  .replace(/html/g, / {0,3}<[^\n>]+>\n/)
  .replace(/table/g, / {0,3}\|?(?:[:\- ]*\|)+[\:\- ]*\n/)
  .getRegex();
const BLOCK_PARAGRAPH_SRC = /^([^\n]+(?:\n(?!hr|heading|lheading|blockquote|fences|list|html|table|[ \t]+\n)[^\n]+)*)/;
function paragraphWith(listPattern) {
  return compose(BLOCK_PARAGRAPH_SRC)
    .replace('hr', BLOCK_HR)
    .replace('heading', ' {0,3}#{1,6}(?:\\s|$)')
    .replace('|lheading', '')
    .replace('|table', '')
    .replace('blockquote', ' {0,3}>')
    .replace('fences', ' {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)')
    .replace('list', listPattern)
    .replace('html', ' {0,3}(?:</?(?:tag)(?: +|\\n|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)')
    .replace('tag', BLOCK_TAGS)
    .getRegex();
}
const BLOCK_TEXT = /^[^\n]+/;
const LABEL_INNER = /(?!\s*\])(?:\\[\s\S]|[^\[\]\\\n]|\n(?![ \t]*\n))+/;
const BLOCK_DEF = compose(/^ {0,3}\[(label)\]: *(?:\n[ \t]*)?([^<\s][^\s]*|<.*?>)(?:(?: +(?:\n[ \t]*)?| *\n[ \t]*)(title))? *(?:\n+|$)/)
  .replace('label', LABEL_INNER)
  .replace('title', /(?:"(?:\\[\s\S]|[^"\\])*"|'(?:\\[\s\S]|[^'\\\n]|\n(?!\n))*'|\((?:\\[\s\S]|[^()\\])*\))/)
  .getRegex();
const BLOCK_LIST = compose(/^(bull)([ \t][^\n]*?)?(?:\n|$)/).replace(/bull/g, BLOCK_BULLET).getRegex();
const HTML_COMMENT = /<!--(?:-?>|[\s\S]*?(?:-->|$))/;
const BLOCK_HTML = compose('^ {0,3}(?:<(script|pre|style|textarea)[\\s>][\\s\\S]*?(?:</\\1>[^\\n]*\\n*|$)|comment[^\\n]*(\\n+|$)|<\\?[\\s\\S]*?(?:\\?>[^\\n]*\\n*|$)|<![A-Z][\\s\\S]*?(?:>[^\\n]*\\n*|$)|<!\\[CDATA\\[[\\s\\S]*?(?:\\]\\]>[^\\n]*\\n*|$)|</?(tag)(?:[ \\t]+|\\n|/?>|$)[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$)|<(?!(?:script|pre|style|textarea)(?![a-z0-9-]))([a-z][a-z0-9-]*)(?:attribute)*? */?>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$)|</[a-z][a-z0-9-]*\\s*>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$))', 'i')
  .replace('comment', HTML_COMMENT)
  .replace('tag', BLOCK_TAGS)
  .replace('attribute', / +[a-zA-Z:_][\w.:-]*(?: *= *"[^"\n]*"| *= *'[^'\n]*'| *= *[^\s"'=<>`]+)?/)
  .getRegex();
const BLOCKQUOTE_INNER_PARA = paragraphWith(/ {0,3}(?:[*+-]|\d{1,9}[.)])(?:[ \t]|\n|$)/);
const BLOCK_BLOCKQUOTE = compose(/^( {0,3}> ?(?:(?![ \t]*(?:\n|$))(paragraph)|[^\n]*)(?:\n|$))+/).replace('paragraph', BLOCKQUOTE_INNER_PARA).getRegex();
const BLOCK_TABLE = compose('^ *([^\\n ].*)\\n {0,3}((?:\\| *)?:?-+:? *(?:\\| *:?-+:? *)*(?:\\| *)?)(?:\\n((?:(?! *\\n|hr|heading|blockquote|code|fences|list|html).*(?:\\n|$))*)\\n*|$)')
  .replace('hr', BLOCK_HR)
  .replace('heading', ' {0,3}#{1,6}(?:\\s|$)')
  .replace('blockquote', ' {0,3}>')
  .replace('code', '(?: {4}| {0,3}\t)[^\\n]')
  .replace('fences', ' {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)')
  .replace('list', ' {0,3}(?:[*+-]|1[.)])[ \\t]')
  .replace('html', ' {0,3}(?:</?(?:tag)(?: +|\\n|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)')
  .replace('tag', BLOCK_TAGS)
  .getRegex();
const BLOCK_PARAGRAPH_GFM = compose(BLOCK_PARAGRAPH_SRC)
  .replace('hr', BLOCK_HR)
  .replace('heading', ' {0,3}#{1,6}(?:\\s|$)')
  .replace('|lheading', '')
  .replace('table', BLOCK_TABLE)
  .replace('blockquote', ' {0,3}>')
  .replace('fences', ' {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)')
  .replace('list', ' {0,3}(?:[*+-]|1[.)])[ \\t]+[^ \\t\\n]')
  .replace('html', ' {0,3}(?:</?(?:tag)(?: +|\\n|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)')
  .replace('tag', BLOCK_TAGS)
  .getRegex();

// --- Sticky versions -------------------------------------------------
// A sticky regex only matches at lastIndex, so a ^ anchor inside it can
// only ever match at position 0 of the whole string. Strip every ^ that
// is not part of a character class (negations such as [^...] are kept).
function stripAnchors(src) {
  let out = '';
  let inClass = false;
  for (let i = 0; i < src.length; i++) {
    const c = src[i];
    if (c === '\\') {
      out += c + (src[i + 1] ?? '');
      i++;
      continue;
    }
    if (c === '[') inClass = true;
    else if (c === ']') inClass = false;
    else if (c === '^' && !inClass) continue;
    out += c;
  }
  return out;
}
function sticky(re) {
  const flags = re.flags.replace(/[gmy]/g, '') + 'y';
  return new RegExp(stripAnchors(re.source), flags);
}
const S_NEWLINE = sticky(BLOCK_NEWLINE);
const S_CODE = sticky(BLOCK_CODE);
const S_FENCES = sticky(BLOCK_FENCES);
const S_HR = sticky(BLOCK_HR);
const S_HEADING = sticky(BLOCK_HEADING);
const S_LHEADING = sticky(BLOCK_LHEADING_GFM);
const S_DEF = sticky(BLOCK_DEF);
const S_LIST = sticky(BLOCK_LIST);
const S_HTML = sticky(BLOCK_HTML);
const S_BLOCKQUOTE = sticky(BLOCK_BLOCKQUOTE);
const S_TABLE = sticky(BLOCK_TABLE);
const S_PARAGRAPH = sticky(BLOCK_PARAGRAPH_GFM);
const S_TEXT = sticky(BLOCK_TEXT);
// Indent-dependent helpers used as plain anchored tests on one line.
function testAt(re, str) { re.lastIndex = 0; return re.exec(str) !== null; }
function execAt(re, str, pos) { re.lastIndex = pos; return re.exec(str); }

// ------------------------------------------------------------------
// Inline grammar (GFM)
// ------------------------------------------------------------------
const LOOKBEHIND_OK = (() => {
  try {
    return !!new RegExp('(?<=1)(?<!1)');
  } catch {
    return false;
  }
})();

const INLINE_ESCAPE = /^\\([!"#$%&'()*+,\-./:;<=>?@\[\]\\^_`{|}~])/;
const INLINE_CODE = /^(`+)([^`]|[^`][\s\S]*?[^`])\1(?!`)/;
const INLINE_BR = /^( {2,}|\\)\n(?!\s*$)[ \t]*/;

// Unicode punctuation classes used by the emphasis machinery.
const PUNCT = /[\p{P}\p{S}]/u;
const PUNCT_SPACE = /[\s\p{P}\p{S}]/u;
const NOT_PUNCT_SPACE = /[^\s\p{P}\p{S}]/u;
const PUNCT_NO_TILDE = /(?!~)[\p{P}\p{S}]/u;
const PUNCT_SPACE_NO_TILDE = /(?!~)[\s\p{P}\p{S}]/u;
const NOT_PUNCT_SPACE_TILDE = /(?:[^\s\p{P}\p{S}]|~)/u;

// A single punctuation-or-space character (but not * or _) at the
// start of a string; used to judge whether a delimiter can open.
const INLINE_PUNCTUATION = compose(/^((?![*_])punctSpace)/, 'u')
  .replace(/punctSpace/g, PUNCT_SPACE)
  .getRegex();

// Masking patterns: spans that emphasis closers must not see inside
// (links, code spans, raw HTML) are blanked out with placeholder text.
const BRACKETED = /\[(?:\\[\s\S]|[^\[\]\\])*\]/;
const BLOCK_SKIP = compose(/link|precode-code|html/, 'g')
  .replace('link', /\[(?:[^\[\]`]|(?<a>`+)[^`]+\k<a>(?!`))*?\]\((?:\\[\s\S]|[^\\\(\)]|\((?:\\[\s\S]|[^\\\(\)])*\))*\)/)
  .replace('precode-', LOOKBEHIND_OK ? '(?<!`)()' : '(^^|[^`])')
  .replace('code', /(?<b>`+)[^`]+\k<b>(?!`)/)
  .replace('html', /<(?! )[^<>]*?>/)
  .getRegex();
const ANY_PUNCT = compose(/\\(punct)/, 'gu').replace(/punct/g, PUNCT).getRegex();
const ANY_PUNCT_OUTSIDE_CODE = compose(/(`+)(?:[^`]|[^`][\s\S]*?[^`])\1(?!`)|`+|\\(punct)/, 'gu')
  .replace(/punct/g, PUNCT)
  .getRegex();

// Emphasis / strikethrough delimiter patterns. The left-delimiter
// patterns match a run of markers plus the one character after it
// (punctuation, or any non-space character); the right-delimiter
// patterns are global scans that walk a masked source looking for a
// run that can close.
const LDELIM_SRC = /^(?:\*+(?:((?!\*)punct)|([^\s*]))?)|^_+(?:((?!_)punct)|([^\s_]))?/;
const LDELIM = compose(LDELIM_SRC, 'u').replace(/punct/g, PUNCT_NO_TILDE).getRegex();
const RDELIM_AST_SRC = '^[^_*]*?__[^_*]*?\\*[^_*]*?(?=__)|[^*]+(?=[^*])|(?!\\*)punct(\\*+)(?=[\\s]|$)|notPunctSpace(\\*+)(?!\\*)(?=punctSpace|$)|(?!\\*)punctSpace(\\*+)(?=notPunctSpace)|[\\s](\\*+)(?!\\*)(?=punct)|(?!\\*)punct(\\*+)(?!\\*)(?=punct)|notPunctSpace(\\*+)(?=notPunctSpace)';
const RDELIM_AST = compose(RDELIM_AST_SRC, 'gu')
  .replace(/notPunctSpace/g, NOT_PUNCT_SPACE_TILDE)
  .replace(/punctSpace/g, PUNCT_SPACE_NO_TILDE)
  .replace(/punct/g, PUNCT_NO_TILDE)
  .getRegex();
const RDELIM_UND_SRC = '^[^_*]*?\\*\\*[^_*]*?_[^_*]*?(?=\\*\\*)|[^_]+(?=[^_])|(?!_)punct(_+)(?=[\\s]|$)|notPunctSpace(_+)(?!_)(?=punctSpace|$)|(?!_)punctSpace(_+)(?=notPunctSpace)|[\\s](_+)(?!_)(?=punct)|(?!_)punct(_+)(?!_)(?=punct)';
const RDELIM_UND = compose(RDELIM_UND_SRC, 'gu')
  .replace(/notPunctSpace/g, NOT_PUNCT_SPACE)
  .replace(/punctSpace/g, PUNCT_SPACE)
  .replace(/punct/g, PUNCT)
  .getRegex();
const DEL_LDELIM = compose(/^~~?(?:((?!~)punct)|[^\s~])/, 'u').replace(/punct/g, PUNCT).getRegex();
const DEL_RDELIM_SRC = '^[^~]+(?=[^~])|(?!~)punct(~~?)(?=[\\s]|$)|notPunctSpace(~~?)(?!~)(?=punctSpace|$)|(?!~)punctSpace(~~?)(?=notPunctSpace)|[\\s](~~?)(?!~)(?=punct)|(?!~)punct(~~?)(?!~)(?=punct)|notPunctSpace(~~?)(?=notPunctSpace)';
const DEL_RDELIM = compose(DEL_RDELIM_SRC, 'gu')
  .replace(/notPunctSpace/g, NOT_PUNCT_SPACE)
  .replace(/punctSpace/g, PUNCT_SPACE)
  .replace(/punct/g, PUNCT)
  .getRegex();

// Autolinks <scheme:...> and <user@host>.
const EMAIL_LOCAL = /[A-Za-z0-9.!#$%&'*+/=?^_`{|}~-]+(@)[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+(?![-_])/;
const INLINE_AUTOLINK = compose(/^<(scheme:[^\s\x00-\x1f<>]*|email)>/)
  .replace('scheme', /[a-zA-Z][a-zA-Z0-9+.-]{1,31}/)
  .replace('email', EMAIL_LOCAL)
  .getRegex();

// Inline HTML tag.
const INLINE_TAG = compose('^comment|^</[a-zA-Z][a-zA-Z0-9-]*\\s*>|^<[a-zA-Z][a-zA-Z0-9-]*(?:attribute)*?\\s*/?>|^<\\?[\\s\\S]*?\\?>|^<![a-zA-Z]+\\s[\\s\\S]*?>|^<!\\[CDATA\\[[\\s\\S]*?\\]\\]>')
  .replace('comment', compose(HTML_COMMENT).replace('(?:-->|$)', '-->').getRegex())
  .replace('attribute', /\s+[a-zA-Z:_][\w.:-]*(?:\s*=\s*"[^"]*"|\s*=\s*'[^']*'|\s*=\s*[^\s"'=<>`]+)?/)
  .getRegex();

// Link label: balanced brackets, backslash escapes, code spans, and
// doubled backticks before a closing bracket are all allowed inside.
const LABEL_BODY = compose(/(?:\[(?:brackets|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\])|[^\[\]\\`])*?/)
  .replace('brackets', BRACKETED)
  .getRegex();
const INLINE_LINK = compose(/^!?\[(label)\]\([ \t\n]*(href)(?:(?:[ \t]+(?:\n[ \t]*)?|\n[ \t]*)(title))?[ \t\n]*\)/)
  .replace('label', LABEL_BODY)
  .replace('href', /<(?:\\.|[^\n<>\\])+>|[^ \t\n\x00-\x1f]+|(?=\))/)
  .replace('title', /"(?:\\[\s\S]|[^"\\])*"|'(?:\\[\s\S]|[^'\\])*'|\((?:\\[\s\S]|[^)\\])*\)/)
  .getRegex();
const INLINE_REFLINK = compose(/^!?\[(label)\]\[(ref)\]/)
  .replace('label', LABEL_BODY)
  .replace('ref', LABEL_INNER)
  .getRegex();
const INLINE_NOLINK = compose(/^!?\[(ref)\](?:\[\])?/)
  .replace('ref', LABEL_INNER)
  .getRegex();
// Search pattern for reference-style links inside a text run (used by
// the masking pass and by the link-in-text check).
const REFLINK_LABEL = compose(/(?:[^\[\]\\`]*(?:\[(?:brackets|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\]))){0,999}?[^\[\]\\`]*?/)
  .replace('brackets', BRACKETED)
  .getRegex();
const REFLINK_REF = /(?!\s*\])(?:\\[\s\S]|[^\[\]\\]){1,999}/;
const REFLINK_SEARCH = compose('reflink|nolink(?!\\()', 'g')
  .replace('reflink', compose(/^!?\[(label)\]\[(ref)\]/).replace('label', REFLINK_LABEL).replace('ref', REFLINK_REF).getRegex())
  .replace('nolink', compose(/^!?\[(ref)\](?:\[\])?/).replace('ref', REFLINK_REF).getRegex())
  .getRegex();

// GFM extended autolinks: bare URLs and e-mail addresses.
const PROTOCOL = /[hH][tT][tT][pP][sS]?|[fF][tT][pP]/;
const EMAIL_FULL = /[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])/;
const EMAIL_SCHEME = compose(/(?:mailto:email|xmpp:email(?:\/[A-Za-z0-9@.]+)?)/).replace(/email/g, EMAIL_FULL).getRegex();
const INLINE_URL = compose(/^emailProtocol|^((?:protocol):\/\/|www\.)(?:[a-zA-Z0-9\-]+\.?)+[^\s<]*|^email/)
  .replace('emailProtocol', EMAIL_SCHEME)
  .replace('protocol', PROTOCOL)
  .replace('email', /[A-Za-z0-9._+-]+(@)[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])/)
  .getRegex();
// Trims trailing punctuation off a bare URL, one pass at a time.
const URL_BACKPEDAL = /(?:[^?!.,:;*_'"~()&]+|\([^)]*\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*_'"~)]+(?!$))+/;

// Sticky inline patterns (single match at the current position).
const S_ESCAPE = sticky(INLINE_ESCAPE);
const S_CODE_SPAN = sticky(INLINE_CODE);
const S_BR = sticky(INLINE_BR);
const S_TAG = sticky(INLINE_TAG);
const S_LINK = sticky(INLINE_LINK);
const S_REFLINK = sticky(INLINE_REFLINK);
const S_NOLINK = sticky(INLINE_NOLINK);
const S_AUTOLINK = sticky(INLINE_AUTOLINK);
const S_URL = sticky(INLINE_URL);
const S_LDELIM = sticky(LDELIM);
const S_DEL_LDELIM = sticky(DEL_LDELIM);

// ------------------------------------------------------------------
// Per-parse state. Everything here is reset by parse() so one call
// can never leak into the next.
// ------------------------------------------------------------------
let links; // normalized label -> { href, title }
let inlineQueue; // entries waiting for their inline pass
let maskStack; // one entry per active inline render (nested renders stack)
let st; // lexer state: { inLink, inRawBlock, linkEmitted, linkParenPossible, top }

// Does a reference-style link's label contain a real link inside it?
// Used while masking, so emphasis never closes across a link boundary.
function linkInText(src) {
  if (!src.includes('[')) return false;
  for (const m of src.matchAll(BLOCK_SKIP)) {
    if (INLINE_LINK.test(m[0]) && src.charAt(m.index - 1) !== '!') return true;
  }
  for (const m of src.matchAll(REFLINK_SEARCH)) {
    const s = m[0];
    const r = s.lastIndexOf('[');
    if (!(s.charAt(0) === '!' || !Object.hasOwn(links, normalizeLabel(s.slice(r + 1, -1)))) &&
        !(r > 1 && linkInText(s.slice(1, r - 1)))) return true;
  }
  return false;
}

// Blank out the parts of a text run that emphasis closers must not see
// (reference links, inline links, code spans, raw HTML), replacing each
// with same-length placeholder text so every index still lines up.
function maskSrc(src) {
  let t = src;
  if (links && src.includes('[')) {
    const search = REFLINK_SEARCH;
    const maskRef = (m) => {
      const o = m.lastIndexOf('[');
      if (!Object.hasOwn(links, normalizeLabel(m.slice(o + 1, -1)))) return m;
      if (o > 1 && m.charAt(0) !== '!') {
        const inner = m.slice(1, o - 1);
        if (linkInText(inner)) {
          return '[' + inner.replace(search, maskRef) + '][' + 'a'.repeat(m.length - o - 2) + ']';
        }
      }
      return '[' + 'a'.repeat(m.length - 2) + ']';
    };
    t = t.replace(search, maskRef);
  }
  t = t.replace(ANY_PUNCT_OUTSIDE_CODE, (m, ticks, off) =>
    off ? '+'.repeat(m.length)
      : ticks ? ticks + m.slice(ticks.length, -ticks.length).replace(/`/g, '+') + ticks
      : m);
  // Each match becomes [aaa...] of the same length.
  t = t.replace(BLOCK_SKIP, (m) => '[' + 'a'.repeat(m.length - 2) + ']');
  return t;
}

// Scan a masked source for the last position a delimiter run could
// close at: the start of the last run of * / _ / ~ whose preceding
// character is not whitespace. Only the last run matters, because the
// closer search never needs to look past it.
function scanClosers(masked) {
  const em = { '*': -1, '_': -1 };
  let del = -1;
  const n = masked.length;
  for (let s = 0; s < n; s++) {
    const ch = masked[s];
    if (ch !== '*' && ch !== '_' && ch !== '~') continue;
    const prev = s === 0 ? '\n' : masked[s - 1];
    let i = s + 1;
    for (; i < n && masked[i] === ch;) i++;
    if (prev !== ' ' && prev !== '\t' && prev !== '\n' && prev !== '\r' && prev !== '\f') {
      if (ch === '~') del = s;
      else em[ch] = s;
    }
    s = i - 1;
  }
  return { masked, em, del };
}
function lastEmCloser(masked, delim) {
  const top = maskStack.at(-1);
  if (top && top.masked === masked) {
    if (!top.scan) top.scan = scanClosers(masked);
    return top.scan.em[delim];
  }
  return scanClosers(masked).em[delim];
}
function lastDelCloser(masked) {
  const top = maskStack.at(-1);
  if (top && top.masked === masked) {
    if (!top.scan) top.scan = scanClosers(masked);
    return top.scan.del;
  }
  return scanClosers(masked).del;
}

// ------------------------------------------------------------------
// scanText: the plain-text fast path.
//
// Walks a run of ordinary text and returns the index just past it.
// It stops (without consuming) before anything another tokenizer must
// see: a backslash, <, !, [, backtick, *, ~ or _; a hard break; the
// start of a bare URL (http://, https://, ftp://, www. with a valid
// lookbehind, mailto:/xmpp:); or the start of an e-mail address. The
// character just before a hard break, a mailto: link, or an e-mail
// address is included in the run, matching the reference behaviour.
// ------------------------------------------------------------------
const WWW_PREV = /[\s*_~(]/;
function emailStartsAt(src, q, end) {
  let j = q;
  while (j < end && isEmailCharCode(src.charCodeAt(j))) j++;
  return j > q && j < end && src[j] === '@';
}
function protocolAt(src, q) {
  const c0 = src.charCodeAt(q);
  if (c0 === 104 || c0 === 72) { // h H
    if ((src[q + 1] === 't' || src[q + 1] === 'T') &&
        (src[q + 2] === 't' || src[q + 2] === 'T') &&
        (src[q + 3] === 'p' || src[q + 3] === 'P')) {
      let k = q + 4;
      if (src[k] === 's' || src[k] === 'S') k++;
      return src[k] === ':' && src[k + 1] === '/' && src[k + 2] === '/';
    }
    return false;
  }
  if (c0 === 102 || c0 === 70) { // f F
    return (src[q + 1] === 't' || src[q + 1] === 'T') &&
      (src[q + 2] === 'p' || src[q + 2] === 'P') &&
      src[q + 3] === ':' && src[q + 4] === '/' && src[q + 5] === '/';
  }
  return false;
}
function wwwAt(src, q) {
  if (src[q] !== 'w' || src[q + 1] !== 'w' || src[q + 2] !== 'w' || src[q + 3] !== '.') return false;
  return q === 0 || WWW_PREV.test(src[q - 1]);
}
function hardBreakAt(src, q, end) {
  if (src[q] !== ' ') return false;
  let j = q;
  while (j < end && src[j] === ' ') j++;
  return j - q >= 2 && src[j] === '\n';
}
function scanText(src, pos, end) {
  if (pos >= end) return pos;
  // A lone non-alphanumeric character directly before mailto:/xmpp:
  // is its own one-character run, so the scheme gets linked next.
  if (!isAlnumCode(src.charCodeAt(pos)) &&
      (src.startsWith('mailto:', pos + 1) || src.startsWith('xmpp:', pos + 1))) {
    return pos + 1;
  }
  // First character: a run of backticks, a run of tildes, or one char.
  let q = pos;
  const f0 = src[q];
  if (f0 === '`' || f0 === '~') {
    while (q < end && src[q] === f0) q++;
  } else {
    q++;
  }
  // Stops that apply immediately after the first character.
  if (q < end) {
    if (src[q] === '`' || src[q] === '~') return q;
    if (hardBreakAt(src, q, end)) return q;
    if (emailStartsAt(src, q, end)) return q;
  }
  for (; q < end; q++) {
    const ch = src[q];
    const code = src.charCodeAt(q);
    if (code < 128 && TEXT_STOP[code]) return q;
    if (protocolAt(src, q)) return q;
    if (ch === 'w' && wwwAt(src, q)) return q;
    if (ch !== ' ' && hardBreakAt(src, q + 1, end)) return q + 1;
    if (!isAlnumCode(code) &&
        (src.startsWith('mailto:', q + 1) || src.startsWith('xmpp:', q + 1))) return q + 1;
    if (!isEmailCharCode(code) && emailStartsAt(src, q + 1, end)) return q + 1;
  }
  return end;
}

// ------------------------------------------------------------------
// Block tokenizers. Each takes (src, pos) and returns a token object
// (with .raw) or null. The caller advances by token.raw.length.
// ------------------------------------------------------------------
function queueInline(src, owner) {
  const q = { src, owner, prefix: '' };
  inlineQueue.push(q);
  owner.q = q;
  return q;
}

function fenceText(raw, content) {
  const m = raw.match(RX.indentCodeCompensation);
  if (m === null) return content;
  const indent = m[1];
  return content.split('\n').map((line) => {
    const lead = line.match(RX.beginningSpace);
    if (lead === null) return line;
    return line.slice(Math.min(lead[0].length, indent.length));
  }).join('\n');
}

function spaceTok(src, pos) {
  const m = execAt(S_NEWLINE, src, pos);
  if (m && m[0].length > 0) return { type: 'space', raw: m[0] };
  return null;
}
function codeTok(src, pos) {
  const m = execAt(S_CODE, src, pos);
  if (!m) return null;
  const text = trimBlankTail(m[0]).replace(RX.codeRemoveIndent, '');
  return { type: 'code', raw: trimBlankTail(m[0]), codeBlockStyle: 'indented', text };
}
function fencesTok(src, pos) {
  const m = execAt(S_FENCES, src, pos);
  if (!m) return null;
  return {
    type: 'code',
    raw: m[0],
    lang: m[2] ? m[2].trim().replace(ANY_PUNCT, '$1') : m[2],
    text: fenceText(m[0], m[3] || ''),
  };
}
function headingTok(src, pos) {
  const m = execAt(S_HEADING, src, pos);
  if (!m) return null;
  let text = m[2].trim();
  if (RX.endingHash.test(text)) {
    const stripped = rtrim(text, '#');
    if (!stripped || RX.endingSpaceTabChar.test(stripped)) text = stripped.trim();
  }
  const tok = { type: 'heading', raw: rtrim(m[0], '\n'), depth: m[1].length, text };
  queueInline(text, tok);
  return tok;
}
function hrTok(src, pos) {
  const m = execAt(S_HR, src, pos);
  if (!m) return null;
  return { type: 'hr', raw: rtrim(m[0], '\n') };
}
function htmlTok(src, pos) {
  const m = execAt(S_HTML, src, pos);
  if (!m) return null;
  const text = trimBlankTail(m[0]);
  return { type: 'html', block: true, raw: text, pre: m[1] === 'pre' || m[1] === 'script' || m[1] === 'style', text };
}
function defTok(src, pos) {
  const m = execAt(S_DEF, src, pos);
  if (!m) return null;
  if (!RX.startAngleBracket.test(m[2]) && findUnbalanced(m[2], '()') !== -1) return null;
  const tag = normalizeLabel(m[1]);
  const href = m[2] ? m[2].replace(RX.hrefBrackets, '$1').replace(ANY_PUNCT, '$1') : '';
  const title = m[3] ? m[3].substring(1, m[3].length - 1).replace(ANY_PUNCT, '$1') : m[3];
  return { type: 'def', tag, raw: rtrim(m[0], '\n'), href, title };
}
function tableTok(src, pos) {
  const m = execAt(S_TABLE, src, pos);
  if (!m || !RX.tableDelimiter.test(m[2])) return null;
  const header = splitCells(m[1]);
  const delims = m[2].replace(RX.tableAlignChars, '').split('|');
  const rowsSrc = m[3]?.trim() ? m[3].replace(RX.tableRowBlankLine, '').split('\n') : [];
  if (header.length !== delims.length) return null;
  const tok = { type: 'table', raw: rtrim(m[0], '\n'), header: [], align: [], rows: [] };
  for (const d of delims) {
    if (RX.tableAlignRight.test(d)) tok.align.push('right');
    else if (RX.tableAlignCenter.test(d)) tok.align.push('center');
    else if (RX.tableAlignLeft.test(d)) tok.align.push('left');
    else tok.align.push(null);
  }
  for (let i = 0; i < header.length; i++) {
    const cell = { text: header[i], header: true, align: tok.align[i] };
    queueInline(header[i], cell);
    tok.header.push(cell);
  }
  for (const row of rowsSrc) {
    tok.rows.push(splitCells(row, tok.header.length).map((text, p) => {
      const cell = { text, header: false, align: tok.align[p] };
      queueInline(text, cell);
      return cell;
    }));
  }
  return tok;
}
function lheadingTok(src, pos) {
  const m = execAt(S_LHEADING, src, pos);
  if (!m) return null;
  const text = m[1].trim();
  const tok = { type: 'heading', raw: rtrim(m[0], '\n'), depth: m[2].charAt(0) === '=' ? 1 : 2, text };
  queueInline(text, tok);
  return tok;
}
function paragraphTok(src, pos) {
  const m = execAt(S_PARAGRAPH, src, pos);
  if (!m) return null;
  const text = m[1].charAt(m[1].length - 1) === '\n' ? m[1].slice(0, -1) : m[1];
  const tok = { type: 'paragraph', raw: m[0], text };
  queueInline(text, tok);
  return tok;
}
function textTok(src, pos) {
  const m = execAt(S_TEXT, src, pos);
  if (!m) return null;
  const tok = { type: 'text', raw: m[0], text: m[0] };
  queueInline(m[0], tok);
  return tok;
}

// Guards that keep the two expensive block patterns (table, setext
// heading) from running when the next lines cannot possibly match.
function maybeTable(src, pos, end) {
  const nl1 = src.indexOf('\n', pos);
  if (nl1 === -1 || nl1 >= end) return false;
  const line2Start = nl1 + 1;
  const nl2 = src.indexOf('\n', line2Start);
  const line2End = nl2 === -1 ? end : nl2;
  for (let i = line2Start; i < line2End; i++) {
    const c = src[i];
    if (c === '|' || c === ':') return true;
  }
  return false;
}
const SETEXT_LINE = /^ {0,3}(=+|-+)[ \t]*\n?$/;
const LHEAD_STOP_BULLET = /^ {0,3}(?:[*+-]|\d{1,9}[.)]) /;
const LHEAD_STOP_FENCES = /^ {0,3}(?:`{3,}|~{3,})/;
const LHEAD_STOP_BLOCKQUOTE = /^ {0,3}>/;
const LHEAD_STOP_HEADING = /^ {0,3}#{1,6}(?:\s|$)/;
const LHEAD_STOP_HR = /^ {0,3}(?:(?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)/;
const LHEAD_STOP_HTML = /^ {0,3}<[^\n>]+>\n/;
const LHEAD_STOP_TABLE = /^ {0,3}\|?(?:[:\- ]*\|)+[:\- ]*\n/;
const BLANK_LINE_NL = /^[ \t]*\n?$/;
function maybeLheading(src, pos, end) {
  // Only the lines of the current paragraph can hold the underline;
  // stop at the first blank line or block-starting line.
  let p = src.indexOf('\n', pos);
  if (p === -1) return false;
  p++;
  while (p < end) {
    const eol = src.indexOf('\n', p);
    const line = eol === -1 ? src.slice(p, end) : src.slice(p, eol + 1);
    if (SETEXT_LINE.test(line)) return true;
    if (BLANK_LINE_NL.test(line)) return false;
    if (LHEAD_STOP_BULLET.test(line)) return false;
    if (LHEAD_STOP_FENCES.test(line)) return false;
    if (LHEAD_STOP_BLOCKQUOTE.test(line)) return false;
    if (LHEAD_STOP_HEADING.test(line)) return false;
    if (LHEAD_STOP_HR.test(line)) return false;
    if (LHEAD_STOP_HTML.test(line)) return false;
    if (LHEAD_STOP_TABLE.test(line)) return false;
    if (eol === -1) return false;
    p = eol + 1;
  }
  return false;
}

function firstLine(src, pos) {
  const nl = src.indexOf('\n', pos);
  return nl === -1 ? src.slice(pos) : src.slice(pos, nl);
}

// Tokenize `src` into `tokens`. `nested` is set for the recursive call
// from a blockquote, where the first paragraph may merge into the
// previous paragraph token. Returns the tokens array.
function blockTokens(src, tokens, nested) {
  let pos = 0;
  const end = src.length;
  let prevLen = Infinity;
  let mergeNext = !!nested;
  while (pos < end) {
    const remain = end - pos;
    if (remain >= prevLen) throw new Error('Infinite loop on byte: ' + src.charCodeAt(pos));
    prevLen = remain;
    const ch = src[pos];
    let t = null;
    if (ch === ' ' || ch === '\t' || ch === '\n') {
      t = spaceTok(src, pos);
      if (t) {
        pos += t.raw.length;
        const last = tokens.at(-1);
        if (t.raw.length === 1 && last !== undefined) last.raw += '\n';
        else tokens.push(t);
        continue;
      }
    }
    if (ch === ' ' || ch === '\t') {
      t = codeTok(src, pos);
      if (t) {
        pos += t.raw.length;
        const last = tokens.at(-1);
        if (last?.type === 'paragraph' || last?.type === 'text') {
          last.raw += (last.raw.endsWith('\n') ? '' : '\n') + t.raw;
          last.text += '\n' + t.text;
          last.q.src = last.text;
        } else tokens.push(t);
        continue;
      }
    }
    if (ch === ' ' || ch === '`' || ch === '~') {
      t = fencesTok(src, pos);
      if (t) { pos += t.raw.length; tokens.push(t); continue; }
    }
    if (ch === ' ' || ch === '#') {
      t = headingTok(src, pos);
      if (t) { pos += t.raw.length; tokens.push(t); continue; }
    }
    if (ch === ' ' || ch === '-' || ch === '_' || ch === '*') {
      t = hrTok(src, pos);
      if (t) { pos += t.raw.length; tokens.push(t); continue; }
    }
    if (ch === ' ' || ch === '>') {
      t = blockquoteTok(src, pos);
      if (t) { pos += t.raw.length; tokens.push(t); continue; }
    }
    if (ch === ' ' || ch === '*' || ch === '+' || ch === '-' || (ch >= '0' && ch <= '9')) {
      t = listTok(src, pos);
      if (t) { pos += t.raw.length; tokens.push(t); continue; }
    }
    if (ch === ' ' || ch === '<') {
      t = htmlTok(src, pos);
      if (t) { pos += t.raw.length; tokens.push(t); continue; }
    }
    if (ch === ' ' || ch === '[') {
      t = defTok(src, pos);
      if (t) {
        pos += t.raw.length;
        const last = tokens.at(-1);
        if (last?.type === 'paragraph' || last?.type === 'text') {
          last.raw += (last.raw.endsWith('\n') ? '' : '\n') + t.raw;
          last.text += '\n' + t.raw;
          last.q.src = last.text;
        } else {
          if (!Object.hasOwn(links, t.tag)) links[t.tag] = { href: t.href, title: t.title };
          tokens.push(t);
        }
        continue;
      }
    }
    if (maybeTable(src, pos, end)) {
      t = tableTok(src, pos);
      if (t) { pos += t.raw.length; tokens.push(t); continue; }
    }
    if (maybeLheading(src, pos, end)) {
      t = lheadingTok(src, pos);
      if (t) { pos += t.raw.length; tokens.push(t); continue; }
    }
    if (st.top) {
      t = paragraphTok(src, pos);
      if (t) {
        pos += t.raw.length;
        const last = tokens.at(-1);
        if (mergeNext && last?.type === 'paragraph') {
          last.raw += (last.raw.endsWith('\n') ? '' : '\n') + t.raw;
          last.text += '\n' + t.text;
          inlineQueue.pop();
          last.q.src = last.text;
        } else tokens.push(t);
        mergeNext = false;
        continue;
      }
    }
    t = textTok(src, pos);
    if (t) {
      pos += t.raw.length;
      const last = tokens.at(-1);
      if (last?.type === 'text') {
        last.raw += (last.raw.endsWith('\n') ? '' : '\n') + t.raw;
        last.text += '\n' + t.text;
        inlineQueue.pop();
        last.q.src = last.text;
      } else tokens.push(t);
      continue;
    }
    throw new Error('Infinite loop on byte: ' + src.charCodeAt(pos));
  }
  st.top = true;
  return tokens;
}

// A blockquote is gathered line by line: lines starting with > (plus
// lazy continuation lines before the first marker) form one chunk,
// which is then tokenized recursively. A chunk that ends in a nested
// blockquote or list is re-parsed together with the lines that follow
// it, so the inner construct can swallow them.
function blockquoteTok(src, pos) {
  const m = execAt(S_BLOCKQUOTE, src, pos);
  if (!m) return null;
  let lines = rtrim(m[0], '\n').split('\n');
  let rawOut = '';
  let textOut = '';
  const tokens = [];
  while (lines.length > 0) {
    let seenMarker = false;
    const chunk = [];
    let p = 0;
    for (p = 0; p < lines.length; p++) {
      if (RX.blockquoteStart.test(lines[p])) {
        chunk.push(lines[p]);
        seenMarker = true;
      } else if (!seenMarker) chunk.push(lines[p]);
      else break;
    }
    lines = lines.slice(p);
    const joined = chunk.join('\n');
    const inner = joined
      .replace(RX.blockquoteMarkerWhitespace, (g, b, m2) => b + expandTabs(m2, b.length))
      .replace(RX.blockquoteSetextReplace, '\n    $1')
      .replace(RX.blockquoteSetextReplace2, '');
    rawOut = rawOut ? rawOut + '\n' + joined : joined;
    textOut = textOut ? textOut + '\n' + inner : inner;
    const savedTop = st.top;
    st.top = true;
    blockTokens(inner, tokens, true);
    st.top = savedTop;
    if (lines.length === 0) break;
    const last = tokens.at(-1);
    if (last?.type === 'code' || last?.type === 'heading' || last?.type === 'hr' ||
        last?.type === 'html' || last?.type === 'table') break;
    if (last?.type === 'blockquote') {
      const rest = lines.join('\n');
      const combined = last.raw + '\n' + rest.replace(RX.blockquoteSetextReplace2, '');
      const reparsed = blockquoteTok(combined, 0);
      tokens[tokens.length - 1] = reparsed;
      const after = combined.substring(reparsed.raw.length).replace(/^\n/, '');
      const leftCount = after ? after.split('\n').length : 0;
      const taken = leftCount ? lines.slice(0, -leftCount) : lines;
      if (taken.length > 0) rawOut = rawOut + '\n' + taken.join('\n');
      textOut = textOut.substring(0, textOut.length - last.text.length) + reparsed.text;
      lines = lines.slice(taken.length);
      if (lines.length > 0 && RX.blockquoteStart.test(lines[0])) continue;
      break;
    } else if (last?.type === 'list') {
      const combined = last.raw + '\n' + lines.join('\n');
      const reparsed = listTok(combined, 0);
      tokens[tokens.length - 1] = reparsed;
      const extra = reparsed.raw.length > last.raw.length
        ? combined.slice(last.raw.length + 1, reparsed.raw.length).split('\n').length : 0;
      if (extra > 0) {
        const y = lines.slice(0, extra).join('\n');
        rawOut = rawOut + '\n' + y;
        textOut = textOut + '\n' + y;
      }
      lines = lines.slice(extra);
      continue;
    }
  }
  return { type: 'blockquote', raw: rawOut, tokens, text: textOut };
}

// A list: the first line fixes the bullet style (ordered or not, and
// . or ) for ordered), then items are collected until a line fails to
// belong to the current item. Item bodies are tokenized recursively
// with top-level paragraph matching disabled, so a tight list renders
// its items without <p> wrappers; a blank line anywhere makes it loose.
function listTok(src, pos) {
  const m = execAt(S_LIST, src, pos);
  if (!m) return null;
  const startPos = pos;
  let cur = pos;
  const end = src.length;
  const marker = m[1].trim();
  const ordered = marker.length > 1;
  const list = {
    type: 'list', raw: '', ordered,
    start: ordered ? +marker.slice(0, -1) : '', loose: false, items: [],
  };
  const bulletPat = ordered ? `\\d{1,9}\\${marker.slice(-1)}` : `\\${marker}`;
  const itemRe = sticky(RX.listItemRegex(bulletPat));
  let sawDoubleBlank = false;
  for (; cur < end;) {
    let skipInner = false;
    let body = '';
    const itemMatch = execAt(itemRe, src, cur);
    if (!itemMatch || execAt(S_HR, src, cur)) break;
    const itemStart = cur;
    cur += itemMatch[0].length;
    const firstRest = itemMatch[2].split('\n', 1)[0];
    const indent = itemMatch[1].length;
    const content = firstRest.replace(RX.leadingSpaceTab, (v) => expandTabs(v, indent));
    let nextLine = firstLine(src, cur);
    let blankItem = !content.trim();
    let width = 0;
    if (blankItem) {
      width = indent + 1;
    } else {
      width = content.search(RX.nonSpaceChar);
      if (width > 4) width = 1;
      body = content.slice(width);
      width += indent;
    }
    if (blankItem && RX.blankLine.test(nextLine)) {
      cur = Math.min(end, cur + nextLine.length + 1);
      skipInner = true;
    }
    if (!skipInner) {
      const nextBullet = RX.nextBulletRegex(width);
      const hrAt = RX.hrRegex(width);
      const fencesAt = RX.fencesBeginRegex(width);
      const headingAt = RX.headingBeginRegex(width);
      const htmlAt = RX.htmlBeginRegex(width);
      const quoteAt = RX.blockquoteBeginRegex(width);
      // `m` is the running line content (first the text after the
      // bullet, then each following line with the item indent cut off);
      // `blankItem` tracks whether the previous line was blank.
      let m = content;
      for (; cur < end;) {
        const line = firstLine(src, cur);
        const expanded = line.replace(RX.leadingSpaceTab, (v) => expandTabs(v, 0));
        if (testAt(fencesAt, line) || testAt(headingAt, line) || testAt(htmlAt, line) ||
            testAt(quoteAt, line) || testAt(nextBullet, line) || testAt(hrAt, line)) break;
        if (expanded.search(RX.nonSpaceChar) >= width || !line.trim()) {
          body += '\n' + expanded.slice(width);
        } else {
          if (blankItem || m.replace(RX.tabCharGlobal, '    ').search(RX.nonSpaceChar) >= 4 ||
              testAt(fencesAt, m) || testAt(headingAt, m) ||
              testAt(htmlAt, m) || testAt(hrAt, m)) break;
          const setext = /^ {0,3}(?:=+|-+) *$/.test(line) &&
            BLOCK_LHEADING_GFM.test(m + '\n' + line);
          body += '\n' + (setext ? '    ' + expanded.replace(/^ {0,3}/, '') : line);
        }
        blankItem = !line.trim();
        cur = Math.min(end, cur + line.length + 1);
        m = expanded.slice(width);
      }
    }
    const itemRaw = src.slice(itemStart, cur);
    if (!list.loose) {
      if (sawDoubleBlank) list.loose = true;
      else if (RX.doubleBlankLine.test(itemRaw)) sawDoubleBlank = true;
    }
    list.items.push({
      type: 'list_item', raw: itemRaw,
      task: RX.listIsTask.test(body), loose: false, text: body, tokens: [],
    });
  }
  const lastItem = list.items.at(-1);
  if (!lastItem) return null;
  lastItem.raw = lastItem.raw.trimEnd();
  lastItem.text = lastItem.text.trimEnd();
  list.raw = src.slice(startPos, cur).trimEnd();
  // Tokenize each item body (paragraphs become plain text tokens
  // unless the list turns out loose) and handle task checkboxes.
  for (const item of list.items) {
    st.top = false;
    item.tokens = blockTokens(item.text, []);
    if (!list.loose) {
      const spaces = item.tokens.filter((g) => g.type === 'space');
      if (spaces.length > 0 && spaces.some((g) => RX.anyLine.test(g.raw))) list.loose = true;
    }
  }
  for (const item of list.items) {
    const first = item.tokens[0];
    if (item.task && (first?.type === 'text' || first?.type === 'paragraph')) {
      item.text = item.text.replace(RX.listReplaceTask, '');
      first.raw = first.raw.replace(RX.listReplaceTask, '');
      first.text = first.text.replace(RX.listReplaceTask, '');
      for (let g = inlineQueue.length - 1; g >= 0; g--) {
        if (RX.listIsTask.test(inlineQueue[g].src)) {
          inlineQueue[g].src = inlineQueue[g].src.replace(RX.listReplaceTask, '');
          break;
        }
      }
      const box = RX.listTaskCheckbox.exec(item.raw);
      if (box) {
        const checked = box[0] !== '[ ]';
        const boxHtml = '<input ' + (checked ? 'checked="" ' : '') + 'disabled="" type="checkbox"> ';
        item.checked = checked;
        if (list.loose) {
          if (item.tokens[0] && (item.tokens[0].type === 'paragraph' || item.tokens[0].type === 'text') && item.tokens[0].q) {
            item.tokens[0].raw = box[0] + ' ' + item.tokens[0].raw;
            item.tokens[0].text = box[0] + ' ' + item.tokens[0].text;
            item.tokens[0].q.prefix = boxHtml;
          } else {
            const para = { type: 'paragraph', raw: box[0] + ' ', text: box[0] + ' ' };
            queueInline('', para);
            para.q.prefix = boxHtml;
            item.tokens.unshift(para);
          }
        } else {
          item.tokens.unshift({ type: 'checkbox', raw: box[0] + ' ', checked });
        }
      }
    } else if (item.task) item.task = false;
  }
  if (list.loose) {
    for (const item of list.items) {
      item.loose = true;
      for (const tok of item.tokens) if (tok.type === 'text') tok.type = 'paragraph';
    }
  }
  return list;
}

// ------------------------------------------------------------------
// Inline rendering. Renders straight into `out` (no token tree);
// link labels and emphasis interiors are rendered by recursive calls
// that share the lexer state, exactly as the reference tokeniser does.
// `mode` 0 renders HTML, 1 renders plain text (image alt text).
// ------------------------------------------------------------------
function renderInline(src, mode) {
  const savedParen = st.linkParenPossible;
  st.linkParenPossible = savedParen && src.includes(')');
  const masked = (src.includes('*') || src.includes('_') || src.includes('~')) ? maskSrc(src) : src;
  maskStack.push({ masked, scan: null });
  const out = [];
  try {
    renderInlineInto(src, masked, out, mode);
  } finally {
    maskStack.pop();
    st.linkParenPossible = savedParen;
  }
  return out.join('');
}

// Does a link label contain a raw HTML tag or autolink that runs past
// the end of the label? Such a label can never be a link.
function labelHasTag(remaining, label, offset) {
  if (!label.includes('<')) return false;
  for (let s = 0; s < label.length; s++) {
    if (label[s] === '\\') { s++; continue; }
    if (label[s] === '`') {
      const code = INLINE_CODE.exec(label.slice(s));
      if (code) { s += code[0].length - 1; continue; }
    }
    if (label[s] !== '<') continue;
    const rest = remaining.slice(offset + s);
    const tag = INLINE_TAG.exec(rest) || INLINE_AUTOLINK.exec(rest);
    if (tag) {
      if (tag[0].length > label.length - s) return true;
      s += tag[0].length - 1;
    }
  }
  return false;
}

// Shared tail of link and reference-link handling: render the label
// (HTML for a link, plain text for an image), honouring the rule that
// a link whose label itself contains a link is not a link at all.
// Returns false when the construct must fall through to plain text.
function emitLink(labelText, href, title, isImage, out, mode) {
  const labelMode = isImage ? 1 : mode;
  const savedInLink = st.inLink;
  const savedEmitted = st.linkEmitted;
  const savedRaw = st.inRawBlock;
  st.inLink = true;
  st.linkEmitted = false;
  const labelRendered = renderInline(labelText, labelMode);
  const emitted = st.linkEmitted;
  st.linkEmitted = savedEmitted;
  st.inLink = savedInLink;
  if (!isImage) {
    if (emitted) {
      st.inRawBlock = savedRaw;
      return false;
    }
    st.linkEmitted = true;
  }
  if (isImage) {
    if (mode === 1) {
      out.push(labelRendered);
    } else {
      const cleaned = cleanUrl(href);
      if (cleaned === null) {
        out.push(escHtml(labelRendered));
      } else {
        let img = '<img src="' + escHtml(cleaned) + '" alt="' + escHtml(labelRendered) + '"';
        if (title) img += ' title="' + escHtml(title) + '"';
        out.push(img + '>');
      }
    }
  } else if (mode === 1) {
    out.push(labelRendered);
  } else {
    const cleaned = cleanUrl(href);
    if (cleaned === null) {
      out.push(labelRendered);
    } else {
      let a = '<a href="' + escHtml(cleaned) + '"';
      if (title) a += ' title="' + escHtml(title) + '"';
      out.push(a + '>' + labelRendered + '</a>');
    }
  }
  return true;
}

// Inline link or image [text](href "title"). Returns the number of
// source characters consumed, or null when this is not a link.
function tryLink(src, pos, out, mode) {
  if (!st.linkParenPossible) return null;
  const m = execAt(S_LINK, src, pos);
  if (!m) return null;
  const isImage = m[0].charAt(0) === '!';
  if (labelHasTag(src.slice(pos), m[1], isImage ? 2 : 1)) return null;
  const hrefTrimmed = m[2].trim();
  if (RX.startAngleBracket.test(hrefTrimmed)) {
    if (!RX.endAngleBracket.test(hrefTrimmed)) return null;
    const stripped = rtrim(hrefTrimmed.slice(0, -1), '\\');
    if ((hrefTrimmed.length - stripped.length) % 2 === 0) return null;
  } else {
    const unbal = findUnbalanced(m[2], '()');
    if (unbal === -2) return null;
    if (unbal > -1) {
      const h = (m[0].indexOf('!') === 0 ? 5 : 4) + m[1].length + unbal;
      m[2] = m[2].substring(0, unbal);
      m[0] = m[0].substring(0, h).trim();
      m[3] = '';
    }
  }
  const strippedRaw = rtrim(m[0].slice(0, -1), '\\');
  if ((m[0].length - strippedRaw.length) % 2 === 0) return null;
  let href = m[2].trim();
  if (RX.startAngleBracket.test(href)) href = href.slice(1, -1);
  href = href.replace(ANY_PUNCT, '$1');
  const title = (m[3] ? m[3].slice(1, -1) : '').replace(ANY_PUNCT, '$1');
  const labelText = m[1].replace(RX.outputLinkReplace, '$1');
  if (!emitLink(labelText, href, title, isImage, out, mode)) return null;
  return m[0].length;
}

// Reference link [text][ref] or shortcut [text]. Returns the number of
// source characters consumed, or null when this is not a link. When the
// reference is undefined, only the opening character is emitted as
// plain text (and the caller advances by one).
function tryReflink(src, pos, out, mode) {
  let m = execAt(S_REFLINK, src, pos);
  if (!m) m = execAt(S_NOLINK, src, pos);
  if (!m) return null;
  const isImage = m[0].charAt(0) === '!';
  if (labelHasTag(src.slice(pos), m[1], isImage ? 2 : 1)) return null;
  const ref = links[normalizeLabel(m[2] || m[1])];
  if (!ref) {
    const ch = m[0].charAt(0);
    out.push(mode === 0 ? escHtml(ch) : ch);
    return 1;
  }
  const labelText = m[1].replace(RX.outputLinkReplace, '$1');
  if (!emitLink(labelText, ref.href, ref.title || null, isImage, out, mode)) return null;
  return m[0].length;
}

// Bare URL / e-mail autolink (GFM). Trailing punctuation is trimmed
// back one pass at a time until the tail is stable.
function tryUrl(src, pos, out, mode) {
  const m = execAt(S_URL, src, pos);
  if (!m) return null;
  let text;
  let href;
  if (m[2] === '@') {
    text = m[0];
    href = 'mailto:' + m[0];
  } else {
    let cur = m[0];
    let prev;
    do {
      prev = cur;
      const b = URL_BACKPEDAL.exec(cur);
      cur = b ? b[0] : '';
    } while (prev !== cur);
    text = cur;
    href = m[1] === 'www.' ? 'http://' + cur : cur;
  }
  if (mode === 1) {
    out.push(text);
  } else {
    const cleaned = cleanUrl(href);
    if (cleaned === null) out.push(escHtml(text, true));
    else out.push('<a href="' + escHtml(cleaned, true) + '">' + escHtml(text, true) + '</a>');
  }
  return text.length;
}

// Explicit autolink <scheme:...> or <user@host>.
function tryAutolink(src, pos, out, mode) {
  const m = execAt(S_AUTOLINK, src, pos);
  if (!m) return null;
  const text = m[1];
  const href = m[2] === '@' ? 'mailto:' + m[1] : m[1];
  if (mode === 1) {
    out.push(text);
  } else {
    const cleaned = cleanUrl(href);
    if (cleaned === null) out.push(escHtml(text, true));
    else out.push('<a href="' + escHtml(cleaned, true) + '">' + escHtml(text, true) + '</a>');
  }
  return m[0].length;
}

// Emphasis / strong emphasis. `prevChar` is the last character of the
// previous plain-text run ('' at the start). Returns the number of
// source characters consumed, or null when no emphasis opens here.
function tryEmStrong(src, masked, pos, prevChar, out, mode) {
  const s = execAt(S_LDELIM, src, pos);
  if (!s || (!s[1] && !s[2] && !s[3] && !s[4])) return null;
  const delim = s[0][0];
  const prevIsDelim = prevChar === delim;
  let l = pos;
  while (l > 0 && masked[l - 1] === delim) l--;
  const p = lastCodePoint(masked.slice(Math.max(0, l - 2), l));
  const h = p === '*' || p === '_' || INLINE_PUNCTUATION.test(p);
  let prev = prevChar;
  if (l < pos) prev = p;
  const u = l < pos ? h : INLINE_PUNCTUATION.test(prev);
  if (s[4] && RX.unicodeAlphaNumeric.test(prev)) return null;
  const d = s[1] || s[3] || '';
  if (d && prev && !u) return null;
  const k = codePointLen(s[0]) - 1;
  let m = k;
  let f = 0;
  const y = pos - l + k;
  const R = p.trim() !== '' && (!!d || (delim === '*' && !h));
  if (delim !== '*' && delim !== '_') return null;
  const closerRe = delim === '*' ? RDELIM_AST : RDELIM_UND;
  const v = lastEmCloser(masked, delim);
  const Q = pos + k;
  if (v < Q) return null;
  const sliced = masked.slice(pos + k);
  const limit = v - Q;
  let match;
  closerRe.lastIndex = 0;
  while ((match = closerRe.exec(sliced)) !== null && !(match.index > limit)) {
    const g = match[1] || match[2] || match[3] || match[4] || match[5] || match[6];
    if (!g) continue;
    const b = codePointLen(g);
    if (match[3] || match[4]) {
      m += b;
      continue;
    } else if (match[5] || match[6] || R) {
      if (prevIsDelim && (match[5] || match[6])) break;
      if (y % 3 && !((y + b) % 3)) {
        f += b;
        continue;
      }
    }
    m -= b;
    if (m > 0) continue;
    const blen = Math.min(b, b + m + f);
    const te = firstCodePoint(match[0]).length;
    const rawLen = k + match.index + te + blen;
    const raw = src.slice(pos, pos + rawLen);
    if (Math.min(k, blen) % 2) {
      if (mode === 0) out.push('<em>');
      out.push(renderInline(raw.slice(1, -1), mode));
      if (mode === 0) out.push('</em>');
    } else {
      if (mode === 0) out.push('<strong>');
      out.push(renderInline(raw.slice(2, -2), mode));
      if (mode === 0) out.push('</strong>');
    }
    return rawLen;
  }
  return null;
}

// Strikethrough ~~text~~. The closing run must have exactly the same
// number of tildes as the opening run.
function tryDel(src, masked, pos, prevChar, out, mode) {
  const s = execAt(S_DEL_LDELIM, src, pos);
  if (!s) return null;
  // The character after the opening run is punctuation and the
  // previous character is alphanumeric: cannot open here.
  if ((s[1] || '') && prevChar && !INLINE_PUNCTUATION.test(prevChar)) return null;
  const o = codePointLen(s[0]) - 1;
  let p = o;
  const u = lastDelCloser(masked);
  const d = pos + o;
  if (u < d) return null;
  const sliced = masked.slice(pos + o);
  const limit = u - d;
  let match;
  DEL_RDELIM.lastIndex = 0;
  while ((match = DEL_RDELIM.exec(sliced)) !== null && !(match.index > limit)) {
    const g = match[1] || match[2] || match[3] || match[4] || match[5] || match[6];
    if (!g) continue;
    const l = codePointLen(g);
    if (l !== o) continue;
    if (match[3] || match[4]) {
      p += l;
      continue;
    }
    p -= l;
    if (p > 0) continue;
    const blen = Math.min(l, l + p);
    const te = firstCodePoint(match[0]).length;
    const rawLen = o + match.index + te + blen;
    const raw = src.slice(pos, pos + rawLen);
    if (mode === 0) out.push('<del>');
    out.push(renderInline(raw.slice(o, -o), mode));
    if (mode === 0) out.push('</del>');
    return rawLen;
  }
  return null;
}

function renderInlineInto(src, masked, out, mode) {
  const end = src.length;
  let pos = 0;
  let prevChar = '';
  let wasText = false;
  while (pos < end) {
    // Like the reference loop: the previous character is only the last
    // character of a plain-text run. After any other token (code span,
    // link, escape, ...) it resets to ''.
    if (!wasText) prevChar = '';
    wasText = false;
    const ch = src[pos];
    if (ch === '\\') {
      const esc = execAt(S_ESCAPE, src, pos);
      if (esc) {
        out.push(mode === 0 ? escHtml(esc[1]) : esc[1]);
        pos += esc[0].length;
        continue;
      }
      const br = execAt(S_BR, src, pos);
      if (br) {
        if (mode === 0) out.push('<br>');
        pos += br[0].length;
        continue;
      }
    } else if (ch === '<') {
      const tag = execAt(S_TAG, src, pos);
      if (tag) {
        if (!st.inLink && RX.startATag.test(tag[0])) st.inLink = true;
        else if (st.inLink && RX.endATag.test(tag[0])) st.inLink = false;
        if (!st.inRawBlock && RX.startPreScriptTag.test(tag[0])) st.inRawBlock = true;
        else if (st.inRawBlock && RX.endPreScriptTag.test(tag[0])) st.inRawBlock = false;
        out.push(tag[0]);
        pos += tag[0].length;
        continue;
      }
      const auto = tryAutolink(src, pos, out, mode);
      if (auto !== null) {
        pos += auto;
        continue;
      }
    } else if (ch === '[' || ch === '!') {
      const link = tryLink(src, pos, out, mode);
      if (link !== null) {
        pos += link;
        continue;
      }
      const ref = tryReflink(src, pos, out, mode);
      if (ref !== null) {
        pos += ref;
        continue;
      }
    } else if (ch === '*' || ch === '_') {
      const em = tryEmStrong(src, masked, pos, prevChar, out, mode);
      if (em !== null) {
        pos += em;
        continue;
      }
      // A failed emphasis delimiter must not swallow a GFM autolink:
      // '*', '_' and '~' are all legal e-mail local-part characters,
      // and the reference tries the URL tokenizer after emphasis fails.
      if (!st.inLink) {
        const url = tryUrl(src, pos, out, mode);
        if (url !== null) {
          pos += url;
          continue;
        }
      }
    } else if (ch === '`') {
      const code = execAt(S_CODE_SPAN, src, pos);
      if (code) {
        let text = code[2].replace(RX.newLineCharGlobal, ' ');
        if (RX.nonSpaceChar.test(text) && RX.startingSpaceChar.test(text) && RX.endingSpaceChar.test(text)) {
          text = text.substring(1, text.length - 1);
        }
        if (mode === 0) out.push('<code>' + escHtml(text, true) + '</code>');
        else out.push(text);
        pos += code[0].length;
        continue;
      }
    } else if (ch === ' ') {
      const br = execAt(S_BR, src, pos);
      if (br) {
        if (mode === 0) out.push('<br>');
        pos += br[0].length;
        continue;
      }
    } else if (ch === '~') {
      const del = tryDel(src, masked, pos, prevChar, out, mode);
      if (del !== null) {
        pos += del;
        continue;
      }
      if (!st.inLink) {
        const url = tryUrl(src, pos, out, mode);
        if (url !== null) {
          pos += url;
          continue;
        }
      }
    } else if (!st.inLink && isEmailCharCode(src.charCodeAt(pos))) {
      const url = tryUrl(src, pos, out, mode);
      if (url !== null) {
        pos += url;
        continue;
      }
    }
    const runEnd = scanText(src, pos, end);
    if (runEnd === pos) throw new Error('Infinite loop on byte: ' + src.charCodeAt(pos));
    const run = src.slice(pos, runEnd);
    if (mode === 0) {
      out.push(st.inRawBlock ? run : escHtml(unescapeEntities(run)));
    } else {
      out.push(run);
    }
    if (run[run.length - 1] !== '_') prevChar = run[run.length - 1];
    wasText = true;
    pos = runEnd;
  }
}

// ------------------------------------------------------------------
// Block rendering.
// ------------------------------------------------------------------
function tableCell(cell) {
  const tag = cell.header ? 'th' : 'td';
  return (cell.align ? '<' + tag + ' align="' + cell.align + '">' : '<' + tag + '>') +
    cell.html + '</' + tag + '>\n';
}

function renderBlocks(tokens, out) {
  for (const tok of tokens) {
    switch (tok.type) {
      case 'space':
        break;
      case 'hr':
        out.push('<hr>\n');
        break;
      case 'heading':
        out.push('<h' + tok.depth + '>' + tok.html + '</h' + tok.depth + '>\n');
        break;
      case 'code': {
        const lang = (tok.lang || '').match(RX.notSpaceStart)?.[0];
        const text = tok.text ? tok.text.replace(RX.endingNewline, '') + '\n' : '';
        if (lang) {
          out.push('<pre><code class="language-' + escHtml(lang) + '">' + escHtml(text, true) + '</code></pre>\n');
        } else {
          out.push('<pre><code>' + escHtml(text, true) + '</code></pre>\n');
        }
        break;
      }
      case 'table': {
        let head = '';
        for (const cell of tok.header) head += tableCell(cell);
        let body = '';
        for (const row of tok.rows) {
          let cells = '';
          for (const cell of row) cells += tableCell(cell);
          body += '<tr>\n' + cells + '</tr>\n';
        }
        if (body) body = '<tbody>' + body + '</tbody>';
        out.push('<table>\n<thead>\n<tr>\n' + head + '</tr>\n</thead>\n' + body + '</table>\n');
        break;
      }
      case 'blockquote': {
        const inner = [];
        renderBlocks(tok.tokens, inner);
        out.push('<blockquote>\n' + inner.join('') + '</blockquote>\n');
        break;
      }
      case 'list': {
        let items = '';
        for (const item of tok.items) {
          const inner = [];
          renderBlocks(item.tokens, inner);
          items += '<li>' + inner.join('') + '</li>\n';
        }
        const tag = tok.ordered ? 'ol' : 'ul';
        const start = tok.ordered && tok.start !== 1 ? ' start="' + tok.start + '"' : '';
        out.push('<' + tag + start + '>\n' + items + '</' + tag + '>\n');
        break;
      }
      case 'checkbox':
        out.push('<input ' + (tok.checked ? 'checked="" ' : '') + 'disabled="" type="checkbox"> ');
        break;
      case 'html':
        out.push(tok.text);
        break;
      case 'def':
        break;
      case 'paragraph':
        out.push('<p>' + tok.html + '</p>\n');
        break;
      case 'text':
        out.push(tok.html);
        break;
      default:
        throw new Error('Token with "' + tok.type + '" type was not found.');
    }
  }
}

// ------------------------------------------------------------------
// Public entry point.
// ------------------------------------------------------------------
export function parse(markdown) {
  links = Object.create(null);
  inlineQueue = [];
  maskStack = [];
  st = { inLink: false, inRawBlock: false, linkEmitted: false, linkParenPossible: true, top: true };
  const src = markdown.replace(RX.carriageReturn, '\n');
  const tokens = blockTokens(src, [], false);
  // Second pass: render the inline content of every token now that
  // all link-reference definitions have been collected.
  for (const q of inlineQueue) {
    st.inRawBlock = false;
    q.owner.html = (q.prefix || '') + renderInline(q.src, 0);
  }
  inlineQueue = [];
  const out = [];
  renderBlocks(tokens, out);
  return out.join('');
}
