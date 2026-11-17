# Covering a disk with disks

## Status

- r(1) = 1 and r(2) ≤ 1 are proved in Lean (`DiskCoveringOne.lean`).
- r(2) ≥ 1, r(3) ≤ √3/2, r(4) ≤ √2/2 and r(7) ≤ 1/2 are proved in Lean (`DiskCoveringSmall.lean`). The upper bounds use the optimal coverings with explicit centers: each point of the unit disk is rotated into the sector nearest one center, where the covering inequality reduces to a polynomial one that `nlinarith` proves, using √3² = 3 for the rotations. The lower bounds r(3) ≥ √3/2, r(4) ≥ √2/2 and r(7) ≥ 1/2 need an argument about the arcs of the unit circle each disk covers, which isn't formalized yet.
- `scripts/generate_images.py` draws these coverings for n = 3, 4 and 7, checking the radius against the exact value and the coverage on a fine grid.
- The witness checker uses exact rational arithmetic, refining squares until each lies in a disk. Optimal coverings are tight (three disk boundaries, or two and the unit circle, meet at a point), so the checker can't certify an optimal radius itself, only one rounded up: for example 7 disks of radius 0.50001 in the hexagonal arrangement pass in well under a second, and 0.49999 fails. So the current records (exact values such as √3/2 for n = 3, and the approximate optima for n = 5, 6, 8 to 10) can't be verified by a witness, and a rounded-up certificate would only be evidence for a weaker bound. No such certificates were added.
- New upper bounds for larger n (where the records aren't known to be optimal) could still be certified, if they improve by more than the rounding.

- r(n) >= 1/sqrt(n) for every n, by area, is proved in Lean (`DiskCoveringArea.lean`), with certificates for n = 21 to 25, which had no lower bound. It uses Mathlib's `EuclideanSpace.volume_closedBall_fin_two` and `measure_iUnion_fintype_le`.

## Ideas

- The hexagon bound pi <= n (3 sqrt(3)/2) r^2 holds for n >= 26 (G. Fejes Tóth 1987, for translates), and Bambah and Rogers (1952) give pi <= (n - 1)(3 sqrt(3)/2) r^2 + pi r^2 for every n, which would improve the area bound for n = 21 to 25 (r(21) >= 0.2387). Neither source was read here.

- Exact verification of tight coverings: check the finitely many points where coverage is tight with exact algebraic numbers, including the second-order condition along common tangents, and use the subdivision elsewhere.
- Several literature upper bounds for n = 13 to 24 are given to only 3 digits (≈0.347 and so on). A rounded-up certificate from the published configuration could look like an improvement on those rows when it isn't, so make those rows more precise before certifying them.
