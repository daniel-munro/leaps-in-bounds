# Covering a disk with disks

## Status

- r(1) = 1 and r(2) ≤ 1 are proved in Lean (`DiskCoveringOne.lean`).
- The witness checker uses exact rational arithmetic, refining squares until each lies in a disk. Optimal coverings are tight (three disk boundaries, or two and the unit circle, meet at a point), so the checker can't certify an optimal radius itself, only one rounded up: for example 7 disks of radius 0.50001 in the hexagonal arrangement pass in well under a second, and 0.49999 fails. So the current records (exact values such as √3/2 for n = 3, and the approximate optima for n = 5, 6, 8 to 10) can't be verified by a witness, and a rounded-up certificate would only be evidence for a weaker bound. No such certificates were added.
- New upper bounds for larger n (where the records aren't known to be optimal) could still be certified, if they improve by more than the rounding.

## Ideas

- Exact verification of tight coverings: check the finitely many points where coverage is tight with exact algebraic numbers, including the second-order condition along common tangents, and use the subdivision elsewhere.
- Several literature upper bounds for n = 13 to 24 are given to only 3 digits (≈0.347 and so on). A rounded-up certificate from the published configuration could look like an improvement on those rows when it isn't, so make those rows more precise before certifying them.
