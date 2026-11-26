"""Verify Lean, export dependencies and rebuild the self-contained research page."""
import argparse
import csv
import json
import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = 'https://github.com/wanglu2016/abhilib-gpt/blob/main/'
TABLES = ('steps', 'premises', 'bridges', 'entries', 'sources', 'concepts', 'rules', 'topics')


def read_table(name):
    with (ROOT / 'data' / (name + '.tsv')).open() as stream:
        rows = csv.reader(stream, delimiter='\t')
        next(rows)
        return list(rows)


def run(*args):
    return subprocess.run(args, cwd=ROOT, text=True, check=True, stdout=subprocess.PIPE).stdout


def catalogue():
    entries = {}
    for group in TABLES:
        for key, title, *fields in read_table(group):
            if key in entries:
                raise ValueError(key)
            row = dict(id=key, title=title, group=group)
            entries[key] = row
            if group == 'steps':
                row.update(refs=fields[0].split(), note=next(iter(fields[1:]), ''), decl='本證.' + key.lower())
            elif group in ('premises', 'bridges'):
                row.update(decl=key)
                if group == 'premises':
                    row.update(verse=fields[0], refs=['R10'])
                else:
                    row.update(refs=fields[0].split())
            elif group == 'rules':
                row.update(decl=fields[0], role=fields[1], note=fields[2], refs=fields[3].split())
            elif group == 'entries':
                row.update(decl=fields[0], note=fields[1], refs=fields[2].split())
            elif group == 'sources':
                row.update(locator=fields[0], note=fields[1], url=fields[2])
            else:
                row.update(note=fields[0], refs=fields[1].split())
    assert [key for key in entries if key.startswith('S')] == [f'S{i:02}' for i in range(1, 49)]
    assert [key for key in entries if key.startswith('P')] == [f'P{i:02}' for i in range(1, 17)]
    for row in entries.values():
        for ref in row.get('refs', []):
            if ref not in entries:
                raise ValueError((row['id'], ref))
    return entries


def lean_entries(entries):
    def lean_name(decl):
        return '.'.join(part if part.isascii() else f'«{part}»' for part in decl.split('.'))
    by_name = {lean_name('AbhiLib.' + e['decl']): e for e in entries.values() if 'decl' in e}
    lead = (ROOT / 'tools/Audit.lean').read_text()
    commands = ['#auditLibrary'] + ['#entry ' + name for name in by_name]
    with tempfile.NamedTemporaryFile(suffix='.lean', mode='w') as tmp:
        tmp.write(lead + '\n' + '\n'.join(commands) + '\n')
        tmp.flush()
        output = run('lake', 'env', 'lean', tmp.name)
    reports = [json.loads(line) for line in output.splitlines()]
    assert len(reports) == len(by_name)
    for audit in reports:
        row = by_name[audit['name']]
        file = audit['module'].replace('.', '/') + '.lean'
        start, end = audit['start'], audit['end']
        lines = (ROOT / file).read_text().splitlines()
        if not 1 <= start <= end <= len(lines):
            raise ValueError((audit['name'], start, end))
        row.update(code='\n'.join(lines[start - 1:end]),
                   src=REPO + file + '#L' + str(start),
                   axioms=sorted(audit['axioms']))
        for field, target in [('body', 'calls'), ('type', 'parameters')]:
            row[target] = [by_name[n]['id'] for n in audit[field] if n in by_name and n != audit['name']]
        # Assembly lemmas are also navigable entries, hence not lost from the graph.
    return entries


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    run('lake', 'build')
    for path in (ROOT / 'AbhiLib').rglob('*.lean'):
        if re.search(r'\b(sorry|admit|axiom|native_decide)\b', path.read_text()):
            raise ValueError(f'unreviewed proof escape or global assumption in {path}')
    # Both the library and stand-alone downloads use the same checked Lean declarations.
    classes = (ROOT / 'AbhiLib/分類.lean').read_text()
    reading = (ROOT / 'AbhiLib/譯讀.lean').read_text()
    imported = 'import AbhiLib.«分類»\n'
    if not reading.startswith(imported):
        raise ValueError('Update the standalone export when changing the translation imports.')
    signature = classes + '\n' + reading.removeprefix(imported).lstrip()
    module = 'export const signature = ' + json.dumps(signature, ensure_ascii=False) + ';\n'
    browser_model = ROOT / 'docs/translate/model.mjs'
    if args.check:
        if browser_model.read_text() != module:
            raise SystemExit('Translation signature differs. Run python3 tools/build.py.')
    else:
        browser_model.write_text(module)
    entries = lean_entries(catalogue())
    model = json.loads(run('lake', 'env', 'lean', '--run', 'tools/Models.lean'))
    assert len(model['rows']) == 112 and len({tuple(r['features']) for r in model['rows']}) == 112
    assert [len(x) for x in model['readings']] == [6, 7, 6]
    trans = json.loads((ROOT / 'data/simplified.json').read_text())
    data = dict(entries=entries, model=model, translation=trans)
    payload = json.dumps(data, ensure_ascii=False, separators=(',', ':')).replace('<', r'\u003c')
    template = (ROOT / 'tools/page.html').read_text()
    assert template.count('/*:DATA:*/') == 1
    html = template.replace('/*:DATA:*/', payload)
    path = ROOT / 'docs/index.html'
    if args.check:
        run('node', 'tools/test-translate.mjs', '--lean')
        if path.read_text() != html:
            raise SystemExit('Research page differs. Run python3 tools/build.py and commit docs/index.html.')
    else:
        path.write_text(html)
    print(f'{len(entries)} indexed records, 48 article steps, 112 model rows. Checked.')


if __name__ == '__main__':
    main()
