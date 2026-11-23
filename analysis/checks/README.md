# Brute-force checks for `roadmap/RepresentationTheory/CharactersOfGLnOverFiniteFields`

`check_green_gl.py` implements the definitions of the roadmap's `Suggested.lean` literally
(`GL (Fin n) F`, the parabolic subgroups, their unipotent radicals, `psi`, `rootPowerSum`,
Harish–Chandra induction as Tau Ceti's `Subgroup.indClassFun`, the Jacquet restriction, the pairing
`characterPairing`) and evaluates the roadmap's statements on small groups, check by check. The
dictionary between the Lean definitions and the code is at the top of the script. Every check prints
one `ok` / `FAIL` line; the exit code is 1 if a check failed.

```
python3 check_green_gl.py gl2_2 gl2_3 gl2_4 gl2_5 gl2_7 gl2_8 gl2_9 gl3_2     # full checks
python3 check_green_gl.py gl3_3:dc                                          # only the double-coset count
python3 summarize.py LOG... > results.txt                                   # per-case summary
```

Cases are `glN_q`: `GL_n(𝔽_q)`, with `𝔽_q` built inside one field `𝔽_{q^L}`, `L = lcm(1..n)`.
A case suffixed `:dc` runs only the cheapest check (the number of double cosets of two parabolic
subgroups against the number of nonnegative integer matrices with given row and column sums).

What was run (2026-11-23), and where the numbers come from, is recorded in
`ROADMAP-REVIEW.md` §7.9.4; the summary of the runs is `results.txt`.
