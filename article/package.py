#!/usr/bin/env python3
"""Package generated TeX for submission, with immutable theorem-source links."""
from pathlib import Path
import hashlib
import json
import subprocess
import zipfile

ROOT = Path(__file__).resolve().parents[1]
out = ROOT / 'article/verso/_out/submission'
out.mkdir(parents=True, exist_ok=True)
revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
if subprocess.check_output(['git', 'status', '--porcelain', '--', 'counterexample'], cwd=ROOT, text=True):
    raise SystemExit('Commit Isabelle changes before creating immutable source links')
source = (ROOT / 'article/note.tex').read_text().replace('/blob/main/counterexample/', f'/blob/{revision}/counterexample/')
(out / 'note.tex').write_text(source)
with zipfile.ZipFile(out / 'source.zip', 'w', zipfile.ZIP_DEFLATED) as archive:
    archive.writestr('note.tex', source)
(out / 'package.json').write_text(json.dumps({
    'source_revision': revision,
    'entry_point': 'note.tex',
    'sha256': hashlib.sha256((out / 'source.zip').read_bytes()).hexdigest(),
}, indent=2) + '\n')
print(out / 'source.zip')
