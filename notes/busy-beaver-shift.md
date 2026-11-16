# Busy beaver functions (shift and ones)

These notes cover both `busy-beaver-shift` and `busy-beaver-ones`.

## Status

- n = 1 to 5: lower bounds certified by the known champions (BB(5) = 47,176,870 and Σ(5) = 4098 by Marxen and Buntrock's machine `1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA`). The checker simulates step by step, about 4 s for BB(5). The Σ(3) champion (6 ones, 14 steps) differs from the BB(3) champion (21 steps, 5 ones); both were found again by a small tree-normal-form enumeration.
- n = 6, 7: the records (2↑↑2↑↑2↑↑10 and beyond for n = 6) are far beyond simulation, and their values aren't integers the checker can compare. Certifying them needs a proof of the machine's behavior, in Lean against `BusyBeaver.lean`, or checked elsewhere (such as in Coq) and attested. Values would also need a form for up-arrow notation in certificates.

## Upper bounds

The exact values for n ≤ 5 were proved by exhaustive enumeration with non-halting deciders: BB(5) in Coq by bbchallenge (2024). Nothing is in Lean here yet. BB(1) ≤ 1 is a short Lean proof (a 1-state machine that doesn't halt on its first step reads a blank cell forever). BB(2) and beyond need a verified decider for cyclers and translated cyclers, a substantial project.
