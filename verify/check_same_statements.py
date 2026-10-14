#!/usr/bin/env python3
"""Check that Solution.lean proves exactly the statements of Challenge.lean.

The check is on the text of the two files, as a complement to `lake comparator`, which checks
the elaborated statements. It fails unless:

* Challenge.lean contains only imports, comments, `namespace`/`section`/`end`/`open`/`variable`
  commands and theorems whose proof is `sorry`;
* Solution.lean contains only the same kinds of commands, with theorems in place of the
  challenge's, and contains no `sorry`, `admit` or `native_decide` and no `decide +native`;
* the theorems appear in the same order in both files, and each theorem's text from the keyword
  `theorem` to the `:=` that begins its proof, together with any `open ... in` commands in front
  of it, is byte-identical in the two files;
* the commands outside the theorems (imports, namespaces, `open`, `variable`) are identical in
  the two files, so that both statements are read in the same context;
* if comparator.json is present next to the files, its list `theorem_names` is exactly the list
  of the theorems, with their namespace.

Usage: python check_same_statements.py [folder]   (default: the folder of this script)
Uses only the Python standard library.
"""

import json
import os
import re
import sys

CONTEXT_KEYWORDS = ('import', 'namespace', 'section', 'noncomputable section', 'end', 'open',
                    'variable')
OPENERS = {'(': ')', '[': ']', '{': '}', '⦃': '⦄', '⟨': '⟩'}
CLOSERS = set(OPENERS.values())


class CheckError(Exception):
    pass


def comment_mask(text):
    """For each character, whether it lies in a comment (nested block comments, line comments)
    or in a string literal."""
    mask = [False] * len(text)
    i, n = 0, len(text)
    while i < n:
        if text.startswith('/-', i):
            depth, j = 0, i
            while j < n:
                if text.startswith('/-', j):
                    depth += 1
                    j += 2
                elif text.startswith('-/', j):
                    depth -= 1
                    j += 2
                    if depth == 0:
                        break
                else:
                    j += 1
            if depth != 0:
                raise CheckError('unterminated block comment')
            for k in range(i, j):
                mask[k] = True
            i = j
        elif text.startswith('--', i):
            j = text.find('\n', i)
            j = n if j < 0 else j
            for k in range(i, j):
                mask[k] = True
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            for k in range(i, min(j + 1, n)):
                mask[k] = True
            i = j + 1
        else:
            i += 1
    return mask


def chunks(text):
    """Split the file into top-level commands: a command starts at a line whose first character
    is in column 0, is not blank, and does not continue an earlier comment."""
    mask = comment_mask(text)
    starts = []
    pos = 0
    for line in text.split('\n'):
        if line and not line[0].isspace():
            continues_comment = pos > 0 and mask[pos] and mask[pos - 1]
            if not continues_comment:
                starts.append(pos)
        pos += len(line) + 1
    starts.append(len(text))
    result = []
    for a, b in zip(starts, starts[1:]):
        chunk_text = text[a:b]
        chunk_mask = mask[a:b]
        result.append((chunk_text, chunk_mask))
    return result


def code_only(chunk_text, chunk_mask):
    return ''.join(c if not m else ' ' for c, m in zip(chunk_text, chunk_mask))


def split_theorem(chunk_text, chunk_mask):
    """Return (header, body): header is the text up to and including the first `:=` at bracket
    depth 0 outside comments."""
    depth = 0
    for i, c in enumerate(chunk_text):
        if chunk_mask[i]:
            continue
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        elif depth == 0 and chunk_text.startswith(':=', i):
            return chunk_text[:i + 2], chunk_text[i + 2:]
    raise CheckError('theorem without `:=`: ' + chunk_text.split('\n')[0])


def parse(path, is_challenge):
    text = open(path, encoding='utf-8').read()
    theorems = []      # (full name, prefix, header)
    context = []       # commands outside theorems
    namespaces = []
    pending_prefix = []
    for chunk_text, chunk_mask in chunks(text):
        code = code_only(chunk_text, chunk_mask).strip()
        if not code:
            continue   # a comment
        first = code.split('\n')[0]
        if re.match(r'open\b.*\bin$', first) and '\n' not in code:
            pending_prefix.append(chunk_text.rstrip())
            continue
        if re.match(r'theorem\s', code):
            header, body = split_theorem(chunk_text, chunk_mask)
            name = code.split()[1]
            full = '.'.join(namespaces + [name])
            body_code = code_only(body, chunk_mask[len(header):]).strip()
            if is_challenge and body_code != 'sorry':
                raise CheckError(f'{path}: theorem {name} is not closed by `sorry` alone')
            theorems.append((full, tuple(pending_prefix), header))
            pending_prefix = []
            continue
        if pending_prefix:
            raise CheckError(f'{path}: `open ... in` not followed by a theorem: {first}')
        keyword = next((k for k in CONTEXT_KEYWORDS if re.match(re.escape(k) + r'\b', code)),
                       None)
        if keyword is None:
            raise CheckError(f'{path}: command not allowed here: {first}')
        if keyword == 'namespace':
            namespaces += code.split()[1].split('.')
        elif keyword == 'end':
            parts = code.split()
            if len(parts) > 1 and namespaces:
                ended = parts[1].split('.')
                if namespaces[-len(ended):] == ended:
                    del namespaces[-len(ended):]
        context.append(code)
    if pending_prefix:
        raise CheckError(f'{path}: `open ... in` at the end of the file')
    if not is_challenge:
        all_code = code_only(text, comment_mask(text))
        for bad in (r'\bsorry\b', r'\badmit\b', r'\bnative_decide\b', r'\bdecide\s*\+native\b'):
            if re.search(bad, all_code):
                raise CheckError(f'{path}: forbidden token {bad}')
    return theorems, context


def main():
    folder = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__))
    challenge = os.path.join(folder, 'Challenge.lean')
    solution = os.path.join(folder, 'Solution.lean')
    try:
        ch_thms, ch_ctx = parse(challenge, True)
        so_thms, so_ctx = parse(solution, False)
        if ch_ctx != so_ctx:
            for a, b in zip(ch_ctx, so_ctx):
                if a != b:
                    raise CheckError(f'context differs: {a!r} vs {b!r}')
            raise CheckError('context commands differ in number')
        names = [t[0] for t in ch_thms]
        if len(set(names)) != len(names):
            raise CheckError('a theorem name is repeated')
        for i, (a, b) in enumerate(zip(ch_thms, so_thms)):
            if a != b:
                raise CheckError(f'theorem {i + 1} differs: {a[0]} (challenge) vs {b[0]} '
                                 '(solution), or its statement text differs')
        if len(ch_thms) != len(so_thms):
            raise CheckError(f'{len(ch_thms)} theorems in the challenge, '
                             f'{len(so_thms)} in the solution')
        config = os.path.join(folder, 'comparator.json')
        if os.path.exists(config):
            listed = json.load(open(config, encoding='utf-8'))['theorem_names']
            if listed != names:
                missing = sorted(set(names) - set(listed))
                extra = sorted(set(listed) - set(names))
                raise CheckError(f'comparator.json theorem_names differ from the theorems: '
                                 f'missing {missing}, extra {extra} (or order differs)')
    except CheckError as e:
        print('FAIL:', e)
        return 1
    print(f'OK: {len(ch_thms)} theorems with identical statements in the same order.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
