"""Generate the readable page of the sealed statements from verify/Challenge.lean.

    python verify/make_core_page.py            # write verify/CORE.md (and verify/core.tex, core.pdf)
    python verify/make_core_page.py --check    # fail if CORE.md was not generated from Challenge.lean

The page lists every sealed theorem in file order, under the section headings of the file, with
the sentence of its docstring and its name; it ends with the SHA-256 of Challenge.lean (line
endings normalized), so that the page a reader approves is tied to one exact statement file. The
docstrings are the mathematics; `lake comparator` ties each name to its formal statement, and an
independent reading checks that each docstring says what its statement says.
"""
from __future__ import annotations

import hashlib
import re
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
CHALLENGE = HERE / "Challenge.lean"
MD = HERE / "CORE.md"
TEX = HERE / "core.tex"


def digest() -> str:
    return hashlib.sha256(CHALLENGE.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def items() -> list[tuple[str, str, str]]:
    """(kind, title or name, text) in file order; kind is 'section' or 'theorem'."""
    src = CHALLENGE.read_text(encoding="utf-8")
    out = []
    pat = re.compile(r"/-!\s*##\s*(?P<title>[^\n]*?)\s*(?:-/|\n(?P<stext>.*?)-/)"
                     r"|/--(?P<doc>.*?)-/\s*(?:@\[[^\]]*\]\s*)?theorem\s+(?P<name>[^\s({\[]+)", re.S)
    for m in pat.finditer(src):
        if m.group("title") is not None:
            out.append(("section", m.group("title").strip(), " ".join((m.group("stext") or "").split())))
        else:
            out.append(("theorem", m.group("name"), " ".join(m.group("doc").split())))
    return out


MATH = re.compile(r"\$([^$]+)\$([.,;:])?")  # a formula with the punctuation that follows it
RELATION = re.compile(r"(?<![<>!])=|\\le\b|\\ge\b|\\leq|\\geq|\\subseteq|\\iff|\\equiv|(?<!\\)<|(?<!\\)>|\\ne\b")
LARGE = re.compile(r"\\sum|\\int|\\prod|\\frac|\\exp|\\sqrt|\\bigl|\\Bigl")


def is_display(body: str) -> bool:
    """Set a formula on its own lines: a matrix, or a relation (equation, inequality, inclusion) of
    some length, at least 30 symbols, or 18 when it contains a sum, integral, fraction, root or
    exponential. Commands count as one symbol. The statements themselves are not changed."""
    if re.search(r"\\begin\{[a-z]*matrix\}", body):
        return True
    n = len(re.sub(r"\\[A-Za-z]+", "x", re.sub(r"\s+", " ", body)))
    return bool(RELATION.search(body)) and (n >= 30 or (bool(LARGE.search(body)) and n >= 18))


def github_math(s: str) -> str:
    """Inline math in GitHub's protected form $`...`$: in the plain form $...$ Markdown removes the
    backslash before punctuation first (`\\,`, `\\{`, `\\|`, `\\\\`), which breaks thin spaces, braces,
    norms and matrix rows. `\\operatorname{x}` does not render on GitHub and becomes
    `\\mathrm{x}\\,`. A display formula (`is_display`) is set on its own lines, with the punctuation
    that follows it."""
    def one(m: re.Match) -> str:
        body = re.sub(r"\\operatorname\{([^{}]*)\}", r"\\mathrm{\1}\\,", m.group(1))
        if is_display(body):
            return "\n\n```math\n" + body + (m.group(2) or "") + "\n```\n\n"
        return "$`" + body + "`$" + (m.group(2) or "")
    out = MATH.sub(one, s)
    return re.sub(r"\n\n +", "\n\n", out).strip()


def markdown(its) -> str:
    n = sum(k == "theorem" for k, _, _ in its)
    lines = ["# The sealed statements", "",
             f"Generated from `verify/Challenge.lean` by `verify/make_core_page.py`: the {n} statements "
             "that `lake comparator` checks (see the section \"Verification\" of the front page). Each entry gives the "
             "statement in words and the name of its formal version in `Challenge.lean`.", ""]
    k = 0
    for kind, a, b in its:
        if kind == "section":
            lines += [f"## {a}", ""] + ([github_math(b), ""] if b else [])
        else:
            k += 1
            lines += [f"**{k}.** {github_math(b)}  ", f"<sub>`Sealed.{a}`</sub>", ""]
    lines += ["---", "", f"SHA-256 of `verify/Challenge.lean` (LF line endings): `{digest()}`", ""]
    return "\n".join(lines)


def latex(its) -> str:
    def tex(s: str) -> str:
        parts = re.split(r"(\$[^$]*\$[.,;:]?)", s)  # keep math, escape text
        res = []
        for p in parts:
            if p.startswith("$"):
                m = MATH.fullmatch(p)
                res.append(r"\[" + m.group(1) + (m.group(2) or "") + r"\]"
                           if m and is_display(m.group(1)) else p)
            else:
                p = p.replace("\\", r"\textbackslash{}").replace("&", r"\&").replace("%", r"\%").replace("#", r"\#").replace("_", r"\_")
                p = re.sub(r"`([^`]*)`", r"\\texttt{\1}", p)
                res.append(p)
        return "".join(res)
    body, k = [], 0
    for kind, a, b in its:
        if kind == "section":
            body.append(f"\\section*{{{tex(a)}}}" + (f"\n{tex(b)}\n" if b else ""))
        else:
            k += 1
            body.append(f"\\paragraph{{{k}.}} {tex(b)}\\par{{\\footnotesize\\texttt{{Sealed.{a.replace('_', chr(92) + '_')}}}}}\n")
    return ("\\documentclass[11pt]{article}\n\\usepackage[a4paper,margin=2.4cm]{geometry}\n"
            "\\usepackage{amsmath,amssymb}\n\\usepackage[hidelinks]{hyperref}\n"
            "\\newcommand{\\Aql}{\\mathcal{A}_{\\mathrm{ql}}}\n\\setlength{\\parindent}{0pt}\n"
            "\\title{The sealed statements of LocalityLean}\\date{}\n\\begin{document}\\maketitle\n"
            f"These {k} statements are the ones that \\texttt{{lake comparator}} checks. "
            "Each is followed by the name of its formal version in "
            "\\texttt{verify/Challenge.lean}.\n\n" + "\n".join(body) +
            f"\n\\vfill{{\\footnotesize SHA-256 of \\texttt{{verify/Challenge.lean}}: \\texttt{{{digest()}}}}}\n\\end{{document}}\n")


def main() -> int:
    its = items()
    if "--check" in sys.argv:
        import json
        sealed = json.loads((HERE / "comparator.json").read_text(encoding="utf-8"))["theorem_names"]
        on_page = ["Sealed." + a for k, a, _ in its if k == "theorem"]
        if on_page != sealed:
            print("the page and comparator.json list different theorems: "
                  f"{sorted(set(sealed) ^ set(on_page)) or 'same names, different order'}")
            return 1
        ok = MD.exists() and MD.read_text(encoding="utf-8").replace("\r\n", "\n") == markdown(its)
        print("CORE.md is current" if ok else "CORE.md is stale: run python verify/make_core_page.py")
        return 0 if ok else 1
    MD.write_text(markdown(its), encoding="utf-8", newline="\n")
    TEX.write_text(latex(its), encoding="utf-8", newline="\n")
    if shutil.which("latexmk"):
        subprocess.run(["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error", TEX.name],
                       cwd=HERE, capture_output=True)
        subprocess.run(["latexmk", "-c", TEX.name], cwd=HERE, capture_output=True)
    print(f"wrote {MD.name} ({sum(k == 'theorem' for k, _, _ in its)} statements), {TEX.name}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
