# Minimal superpermutations

## Upper bounds by construction

- The standard recursive construction (replace each permutation `p` of `n - 1` symbols, in order of first appearance in the string for `n - 1`, with `p n p`, merging overlaps) has length `1! + 2! + … + n!`. Certified for `n` up to 9 (46233 for `n = 8`, 409113 for `n = 9`). The string for `n = 9` is 409 kB, so it's stored xz-compressed (22 kB). The checker takes a few seconds.
- The records for `n = 8` and `n = 9`, 46205 and 408966, are Egan's construction (`egan-superpermutations`), of length `n! + (n-1)! + (n-2)! + (n-3)! + n - 3`, which uses Williams' Hamilton cycles in a Cayley graph of the symmetric group. Not yet reproduced here; doing so would improve on the recursive construction by 28 and 147.
