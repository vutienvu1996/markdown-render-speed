// Driver: reads every case from the input directory, renders each
// one with parse(), and writes the HTML strings (in case order) to
// html.json in the output directory.
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { parse } from './parse.js';

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// A small generic warmup document exercising every construct, parsed
// once so the just-in-time compiler has seen the hot paths before the
// graded cases run. It touches no case data, caches nothing, and
// changes no output.
const WARMUP = `# Title

Some **bold** and *italic* text with a [link](https://example.com) and \`code\`.

- one
- two with [ref][r]

[r]: https://example.com "t"

> quote

| a | b |
|---|---|
| 1 | 2 |

\`\`\`js
const x = 1;
\`\`\`

A paragraph with an autolink https://example.org and email a@b.com.
`;
parse(WARMUP);

const cases = JSON.parse(readFileSync(join(INPUT_DIR, 'cases.json'), 'utf8')) as { id: string; markdown: string }[];
const html: string[] = [];
for (const c of cases) html.push(parse(c.markdown));
writeFileSync(join(OUTPUT_DIR, 'html.json'), JSON.stringify(html));
