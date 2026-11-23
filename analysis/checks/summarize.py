#!/usr/bin/env python3
"""Summarise check logs produced by check_green_gl.py: per case the number of checks passed / failed,
the failing lines (if any), and the key Mackey lines.  Usage: summarize.py LOG [LOG ...]  (> results.txt)"""
import pathlib
import re
import sys

for log in sys.argv[1:]:
    text = pathlib.Path(log).read_text(errors="replace").splitlines()
    ok = sum(l.startswith("ok    ") for l in text)
    fail = [l for l in text if l.startswith("FAIL  ")]
    case = pathlib.Path(log).stem
    done = [l for l in text if "checks passed" in l]
    timing = [l for l in text if re.search(r"\(GL_\d\(F_\d+\): [\d.]+s\)", l)]
    status = done[-1].strip("= ") if done else "INCOMPLETE: cut by the timeout before the end"
    print(f"### {case}: {ok} checks passed, {len(fail)} failed  ({status})")
    for l in fail:
        print(l)
    for l in text:
        if re.search(r"^ok    (7\.5 .*Mackey, no scalar|7\.5 .*bijections of the multisets|7\.5 .*Mackey term by term|"
                     r"7\.1 .*hcL L n = Ind_|7\.3 |5\.2 .*<psi_1, Psi_1>|6\.1 .*<chi_1, chi_1>|7\.6 |7\.11 .*GL_\d\(F_\d+\)\] #distinct)",
                     l) and "elliptic" not in l:
            print("   " + l[:230])
    for l in timing:
        print("   " + l.strip())
