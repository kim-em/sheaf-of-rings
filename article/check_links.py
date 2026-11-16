#!/usr/bin/env python3
"""Validate named Isabelle references and their generated TeX source links."""
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
source = (ROOT / 'article/verso/Note.lean').read_text()
names = re.findall(r':::theorem "([^"]+)"|\{isabelle "([^"]+)"\}', source)
names = [a or b for a, b in names]
errors = []
if not names:
    errors.append('No Isabelle theorem references found')
tex = (ROOT / 'article/note.tex').read_text()
links = re.findall(r'\\href\{https://github.com/kim-em/sheaf-of-rings/blob/main/counterexample/([^{}]+)\\#L(\d+)\}\{\\nolinkurl\{([^{}]+)\}\}', tex)
if sorted(name for _, _, name in links) != sorted(names):
    errors.append('Generated TeX theorem links differ from Verso references; run make -C article')
for name in names:
    matches = []
    declaration = re.compile(r'\s*(?:theorem|lemma|corollary)\s+' + re.escape(name) + r'\s*:')
    for path in (ROOT / 'counterexample').glob('*.thy'):
        matches.extend((path.name, str(i)) for i, line in enumerate(path.read_text().splitlines(), 1)
                       if declaration.match(line))
    if len(matches) != 1:
        errors.append(f'{name}: expected one declaration, found {len(matches)}')
    elif (matches[0][0], matches[0][1], name) not in links:
        errors.append(f'{name}: generated link is stale (now {matches[0]}); run make -C article')
if errors:
    sys.exit('\n'.join(errors))
print(f'Checked {len(names)} Isabelle references and generated source links')
