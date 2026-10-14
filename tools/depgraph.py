"""Print the import graph of the LocalityLean library as an indented list, grouped by layer.

Usage: python tools/depgraph.py            (prints to stdout)
       python tools/depgraph.py --readme   (rewrites the section between the markers in README.md)

A module's line lists the LocalityLean, LinearAQFT, BosonicLean and FermionicLean modules it
imports directly (Mathlib imports are not listed). Layers follow the directory structure and the
order of the programme: Core (supports, generators, Duhamel, paths, the master lemma, site matrix,
decay, grading) -> Qudit -> Approx -> Fermionic, Bosonic -> QuasiLocal.

Adapted from LinearAQFT tools/depgraph.py (commit 331df10).
"""
import os
import re
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
SRC = os.path.join(ROOT, 'LocalityLean')
LAYERS = ['Core', 'Qudit', 'Approx', 'Fermionic', 'Bosonic', 'QuasiLocal']
LIBS = r'(?:LocalityLean|LinearAQFT|BosonicLean|FermionicLean)'


def modules():
    out = {}
    for dirpath, _, files in os.walk(SRC):
        for f in files:
            if not f.endswith('.lean'):
                continue
            path = os.path.join(dirpath, f)
            name = os.path.relpath(path, ROOT)[:-5].replace(os.sep, '.')
            imps = []
            with open(path, encoding='utf-8') as fh:
                for line in fh:
                    m = re.match(r'import\s+(' + LIBS + r'\.[\w.]+)', line)
                    if m:
                        imps.append(m.group(1))
            out[name] = imps
    return out


def render(mods):
    lines = []
    for layer in LAYERS:
        names = sorted(n for n in mods if n.startswith('LocalityLean.' + layer + '.'))
        if not names:
            continue
        lines.append('- **%s**' % layer)
        for n in names:
            short = n[len('LocalityLean.'):]
            deps = ', '.join(i.replace('LocalityLean.', '') for i in mods[n])
            lines.append('  - `%s`' % short + (' <- ' + deps if deps else ''))
    if not lines:
        lines.append('(no library modules yet)')
    return '\n'.join(lines)


def main():
    text = render(modules())
    if '--readme' in sys.argv:
        readme = os.path.join(ROOT, 'README.md')
        with open(readme, encoding='utf-8') as fh:
            content = fh.read()
        start, end = '<!-- depgraph:start -->', '<!-- depgraph:end -->'
        i, j = content.index(start) + len(start), content.index(end)
        content = content[:i] + '\n' + text + '\n' + content[j:]
        with open(readme, 'w', encoding='utf-8', newline='\n') as fh:
            fh.write(content)
        print('README.md updated.')
    else:
        print(text)


if __name__ == '__main__':
    main()
