# Minimal superpermutations

## Upper bounds by construction

- The standard recursive construction (replace each permutation `p` of `n - 1` symbols, in order of first appearance in the string for `n - 1`, with `p n p`, merging overlaps) has length `1! + 2! + … + n!`. Certified for `n` up to 9 (46233 for `n = 8`, 409113 for `n = 9`). The string for `n = 9` is 409 kB, so it's stored xz-compressed (22 kB). The checker takes a few seconds.
- The records for `n = 8` and `n = 9`, 46205 and 408966, are Egan's construction (`egan-superpermutations`), of length `n! + (n-1)! + (n-2)! + (n-3)! + n - 3`, which uses Williams' Hamilton cycles in a Cayley graph of the symmetric group. Not yet reproduced here; doing so would improve on the recursive construction by 28 and 147.

## Published superpermutations imported (Nov 2026)

The superpermutators repository (github.com/superpermutators/superperm, `superpermutations/<n>/`) keeps the record strings, and certificates now use them for L(6) <= 872, L(7) <= 5906, L(8) <= 46173 and L(9) <= 408966. For n = 8 it has strings shorter than Egan's 46205, added in 2026: 46204 (Raudvere), 46188 and 46173/46174, now in the literature data. No string of length 5905 for n = 7 (Teodorescu, on the Google Group) was in the repository when checked, so that bound is still unverified.
