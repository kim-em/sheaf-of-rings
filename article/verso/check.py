#!/usr/bin/env python3
"""Check generated article outputs."""
from pathlib import Path
import re
import subprocess
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parent
NS = {'x': 'http://www.w3.org/1999/xhtml'}

def pdf(path):
    return ET.fromstring(subprocess.check_output(['pdftotext', '-bbox-layout', str(path), '-']))

tree = pdf(ROOT / '_out/note.pdf')
assert tree.findall('.//x:page', NS), 'Empty PDF'
words = ''.join(w.text or '' for w in tree.findall('.//x:word', NS))
assert 'DocumentpreparedinVerso.' in words, 'Missing Verso credit'
log = (ROOT / '_out/note.log').read_text()
assert 'Overfull' not in log, 'Overfull box'
assert 'undefined references' not in log, 'Unresolved citation'

html = subprocess.check_output(['pdftohtml', '-stdout', '-i', str(ROOT / '_out/note.pdf')], stderr=subprocess.DEVNULL, text=True)
links = re.findall(r'href="https://github.com/kim-em/sheaf-of-rings/blob/main/counterexample/([^"#]+)#L(\d+)"[^>]*>(.*?)</a>', html)
assert len(links) == 6, f'Expected six theorem links, got {len(links)}'
for filename, line, caption in links:
    declaration = (ROOT.parents[1] / 'counterexample' / filename).read_text().splitlines()[int(line)-1]
    match = re.match(r'(?:theorem|corollary|lemma) (\w+)\s*:', declaration)
    assert match and match[1] in caption, (filename, line, caption)

source = (ROOT / 'Note.lean').read_text()
assert not re.search(r'\\(?:begin|end|vspace|hspace|parbox|documentclass)\b|```(?:raw|html|latex|tex)\b', source)
print('PASS: source links, Verso credit, no overfull boxes or unresolved citations, no layout/raw blocks in source')
