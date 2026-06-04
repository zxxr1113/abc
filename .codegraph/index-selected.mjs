import { createRequire } from 'node:module';
const require = createRequire(import.meta.url);
const { CodeGraph } = require('/Users/zhaoxiran/.codegraph/versions/v0.9.4/lib/dist/index.js');
const { initGrammars, loadGrammarsForLanguages } = require('/Users/zhaoxiran/.codegraph/versions/v0.9.4/lib/dist/extraction/grammars.js');
import { execFileSync } from 'node:child_process';
import { resolve } from 'node:path';

const root = resolve(import.meta.dirname, '..');

// Collect only the files we care about
const patterns = [
  'src/proof/cec/',
  'src/base/abci/abcScorr.c',
  'src/base/abci/abcXsim.c',
  'src/base/abc/abc_.c',
  'src/base/abc/abc.h',
  'src/base/abc/abcInt.h',
];

console.log('Collecting file list from git...');
const allFiles = new Set();
for (const p of patterns) {
  const out = execFileSync('git', ['ls-files', p], { cwd: root, encoding: 'utf-8' });
  for (const line of out.trim().split('\n')) {
    if (line) allFiles.add(line);
  }
}

const fileList = [...allFiles].sort();
console.log(`Total files to index: ${fileList.length}`);
for (const f of fileList) console.log(`  ${f}`);

console.log('\nInitializing WASM runtime and loading C grammar...');
await initGrammars();
await loadGrammarsForLanguages(['c']);

console.log('Opening CodeGraph and indexing...');
const cg = await CodeGraph.open(root);
const result = await cg.indexFiles(fileList);
console.log(`\nDone — Indexed: ${result.filesIndexed}, Skipped: ${result.filesSkipped}, Errors: ${result.filesErrored}`);
if (result.errors?.length) {
  for (const e of result.errors) console.error(`  [${e.severity}] ${e.message}`);
}
cg.destroy();
