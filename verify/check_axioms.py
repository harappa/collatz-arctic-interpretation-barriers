#!/usr/bin/env python3
"""Check the axioms reported by verify/Probe.lean for every theorem paper_* of the module CollatzProof.Arctic.Paper.

Run from the root of this repository, after `lake build`:

    lake env lean verify/Probe.lean > probe.txt
    python3 verify/check_axioms.py probe.txt
    lake env lean verify/Probe.lean | python3 verify/check_axioms.py     # the same, reading standard input
    python3 verify/check_axioms.py --self-test                           # test this script on synthetic outputs

The theorems are found by scanning the files CollatzProof/Arctic/Paper*.lean of this repository (comments removed);
they are not listed in this script. The check passes if and only if
 1. the output contains no error message of Lean;
 2. for every theorem paper_* of these files, the output contains exactly one report of `#print axioms` for the name
    Collatz.Arctic.Paper.<name>, and the reported axioms are a subset of [propext, Classical.choice, Quot.sound]
    (in particular, sorryAx and project-specific axioms fail the check);
 3. every other report of `#print axioms` in the output also lists only these three axioms, and no report names a
    theorem paper_* that is not declared in these files.
It prints a summary and ALL OK with exit status 0 if the check passes, and lists the problems with exit status 1
otherwise. Python 3, standard library only; it does not run Lean.
"""
from __future__ import annotations

import argparse
import re
import sys
from collections import Counter
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
PAPER_DIR = ROOT / "CollatzProof" / "Arctic"
NAMESPACE = "Collatz.Arctic.Paper"
ALLOWED = ("propext", "Classical.choice", "Quot.sound")
DECL = re.compile(r"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)?(?:(?:private|protected|noncomputable)[ \t]+)*"
                  r"(?:theorem|lemma)[ \t]+(paper_\w+)", re.M)
DEPENDS = re.compile(r"'([^'\s]+)' depends on axioms: \[([^\]]*)\]")
NO_AXIOMS = re.compile(r"'([^'\s]+)' does not depend on any axioms")
ERROR = re.compile(r"^(?:.*?:\d+:\d+: )?error:.*$", re.M)
WARNING = re.compile(r"^(?:.*?:\d+:\d+: )?warning:.*$", re.M)


def strip_comments(s: str) -> str:
    """Remove Lean comments (`--`, nested `/- -/`); string literals are kept."""
    out, i, n, depth = [], 0, len(s), 0
    while i < n:
        if depth == 0 and s[i] == '"':
            j = i + 1
            while j < n and s[j] != '"':
                j += 2 if s[j] == "\\" else 1
            out.append(s[i:j + 1])
            i = j + 1
            continue
        if s.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0 and s.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth > 0:
            if s[i] == "\n":
                out.append("\n")
            i += 1
            continue
        if s.startswith("--", i):
            j = s.find("\n", i)
            i = n if j < 0 else j
            continue
        out.append(s[i])
        i += 1
    return "".join(out)


def paper_theorems(paper_dir: Path) -> tuple[list[Path], list[str]]:
    files = sorted(paper_dir.glob("Paper*.lean"))
    names: list[str] = []
    for p in files:
        names += DECL.findall(strip_comments(p.read_text(encoding="utf-8")))
    return files, names


def parse(output: str) -> tuple[dict[str, list[tuple[str, ...]]], list[str], int]:
    """The reports of `#print axioms` (name -> list of axiom tuples), the error lines and the number of warnings."""
    reports: dict[str, list[tuple[str, ...]]] = {}
    for m in DEPENDS.finditer(output):
        axioms = tuple(a.strip() for a in m.group(2).split(",") if a.strip())
        reports.setdefault(m.group(1), []).append(axioms)
    for m in NO_AXIOMS.finditer(output):
        reports.setdefault(m.group(1), []).append(())
    errors = [m.group(0).strip() for m in ERROR.finditer(output)]
    return reports, errors, len(WARNING.findall(output))


def check(output: str, names: list[str]) -> tuple[list[str], dict[str, list[tuple[str, ...]]], int]:
    problems: list[str] = []
    reports, errors, warnings = parse(output)
    problems += [f"Lean reported an error: {e}" for e in errors]
    for n, k in sorted(Counter(names).items()):
        if k > 1:
            problems.append(f"{n}: declared {k} times in Paper*.lean")
    expected = {f"{NAMESPACE}.{n}" for n in names}
    for full in sorted(expected):
        k = len(reports.get(full, []))
        if k == 0:
            problems.append(f"{full}: no report of `#print axioms` in the output")
        elif k > 1:
            problems.append(f"{full}: {k} reports of `#print axioms` (expected exactly one)")
    for full, rs in sorted(reports.items()):
        for axioms in rs:
            bad = [a for a in axioms if a not in ALLOWED]
            if bad:
                problems.append(f"{full}: depends on {', '.join(bad)} (allowed: {', '.join(ALLOWED)})")
        if full not in expected and full.rsplit(".", 1)[-1].startswith("paper_"):
            problems.append(f"{full}: reported, but not a theorem paper_* of Paper*.lean in {NAMESPACE}")
    return problems, reports, warnings


def summary(names: list[str], files: list[Path], reports: dict[str, list[tuple[str, ...]]], warnings: int) -> None:
    print(f"Paper*.lean: {len(files)} files ({', '.join(p.name for p in files)}), {len(names)} theorems paper_*")
    total = sum(len(rs) for rs in reports.values())
    print(f"output: {total} reports of `#print axioms`, no error, {warnings} warning(s)")
    sets = Counter(axioms for rs in reports.values() for axioms in rs)
    for axioms, k in sorted(sets.items(), key=lambda x: -x[1]):
        print(f"  {k:4d} x [{', '.join(axioms)}]" if axioms else f"  {k:4d} x no axioms")


def self_test(names: list[str]) -> int:
    """Run `check` on synthetic outputs: the good ones must pass, the bad ones must fail."""
    def out(lines: list[str]) -> str:
        return "\n".join(lines) + "\n"
    full = [f"{NAMESPACE}.{n}" for n in names]
    good = [f"'{f}' depends on axioms: [{', '.join(ALLOWED)}]" for f in full]
    cases: list[tuple[str, str, bool]] = [
        ("all three standard axioms", out(good), True),
        ("one theorem without axioms, one with a subset, one report wrapped over two lines",
         out([f"'{full[0]}' does not depend on any axioms", f"'{full[1]}' depends on axioms: [propext]",
              f"'{full[2]}' depends on axioms: [propext,\n Classical.choice, Quot.sound]"] + good[3:]), True),
        ("sorryAx", out([f"'{full[0]}' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]"] + good[1:]),
         False),
        ("a project-specific axiom", out(good[:-1] + [f"'{full[-1]}' depends on axioms: [propext, Collatz.Arctic.ax]"]),
         False),
        ("a missing report", out(good[1:]), False),
        ("a duplicated report", out(good + good[:1]), False),
        ("an error of Lean", out(["verify/Probe.lean:3:0: error: unknown constant 'Collatz.Arctic.Paper.x'"] + good),
         False),
        ("a report of an undeclared theorem paper_*",
         out(good + [f"'{NAMESPACE}.paper_undeclared' depends on axioms: [propext]"]), False),
        ("another declaration with sorryAx", out(good + ["'Collatz.Arctic.foo' depends on axioms: [sorryAx]"]), False),
        ("empty output", "", False),
    ]
    bad = 0
    for label, text, should_pass in cases:
        problems, _, _ = check(text, names)
        ok = (not problems) == should_pass
        bad += not ok
        print(f"self-test: {label}: {'passes' if not problems else 'fails'} "
              f"({'as expected' if ok else 'UNEXPECTED'})")
    print(f"self-test: {len(cases)} synthetic outputs for the {len(names)} theorems paper_*")
    print("ALL OK" if bad == 0 else f"{bad} problem(s)")
    return 0 if bad == 0 else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("output", nargs="?", default="-",
                    help="a file with the output of `lake env lean verify/Probe.lean` (default: standard input)")
    ap.add_argument("--self-test", action="store_true", help="test this script on synthetic outputs and exit")
    a = ap.parse_args()
    files, names = paper_theorems(PAPER_DIR)
    if not names:
        print(f"no theorem paper_* found in {PAPER_DIR}/Paper*.lean")
        print("1 problem(s)")
        return 1
    if a.self_test:
        return self_test(names)
    text = sys.stdin.read() if a.output == "-" else Path(a.output).read_text(encoding="utf-8")
    problems, reports, warnings = check(text, names)
    if problems:
        for p in problems:
            print(p)
        print(f"{len(problems)} problem(s)")
        return 1
    summary(names, files, reports, warnings)
    print("ALL OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
