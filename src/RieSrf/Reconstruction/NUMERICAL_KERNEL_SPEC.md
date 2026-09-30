# Spec: `numerical_kernel` for `AcbMatrix` (Arb-native numerical kernel)

Target repo: Hecke.jl.  New file `src/RieSrf/Numerics/NumericalKernel.jl`,
plus an `include` line in `src/RieSrf.jl` next to the other
`RieSrf/Numerics/*.jl` includes, plus tests.  Implementer: read this whole
file first; every MUST/SHOULD is normative.

## 1. Purpose and constraints

The reconstruction code (`src/RieSrf/Reconstruction/*.jl`) repeatedly needs
the kernel of a numerically rank-deficient complex matrix whose entries are
Arb balls (`AcbFieldElem`, typically theta values at 200-1000 bits).  The
current pattern converts to `Complex{BigFloat}` or MultiFloats and calls
generic `nullspace`/ad-hoc QR; at 200-300 digits this is slow (boxed MPFR
scalars in generic Julia loops) and discards the ball radii.

A rigorous nullspace over balls is impossible in principle (every ball
matrix contains full-rank matrices, so rank deficiency is undecidable from
the data).  The design is therefore a hybrid, and this split is the heart
of the spec:

- the RANK/PIVOT DECISION is heuristic, made at machine precision from
  midpoints;
- ALL high-precision arithmetic stays in FLINT `acb_mat` routines
  (certified `solve`), never in generic Julia loops over boxed scalars;
- the output carries a CERTIFIED residual bound computed in ball
  arithmetic, so a wrong heuristic decision is detected, not silently
  returned.

Dependencies: Nemo (already a dependency) and the `LinearAlgebra` stdlib
(for the ComplexF64 pivoted QR).  Do NOT add GenericLinearAlgebra,
MultiFloats, ArbNumerics, or any other package.

## 2. API

```julia
    numerical_kernel(A::AcbMatrix; rtol::Real = 1e-10,
                     nullity::Union{Int, Nothing} = nothing,
                     gap::Real = 1e4)
      -> N::AcbMatrix, r::Int, resbound::ArbFieldElem
```

- `N`: n x (n - r) matrix over `base_ring(A)` whose columns span the
  computed kernel (n = ncols(A)).  Shape: up to a row permutation, N is
  [X; I] with I the identity on the free columns.  NOT orthonormal; say so
  in the docstring.
- `r`: the numerical rank used.
- `resbound`: a rigorous upper bound for max_ij |(A*N)_ij|, computed in
  ball arithmetic (see 3.6).  The CALLER judges acceptability; the
  function itself only errors on structural failures (see 3.4, 3.5).
- `rtol`: relative threshold for the rank decision (ignored when `nullity`
  is given).
- `nullity`: if provided, forces r = n - nullity and skips gap detection
  (callers such as the Fay-relation matrices know the expected nullity).
- `gap`: minimum acceptable ratio between the last kept and first dropped
  pivot magnitude when `nullity` is NOT given; below it, error (3.4).

Not exported.  Internal to Hecke, like the rest of RieSrf.  Also provide
the convenience method `numerical_kernel(A::Vector{Vector{AcbFieldElem}};
kw...)` that wraps `matrix(...)` -- the reconstruction scripts build
matrices as vectors of rows.

Add a complete docstring stating the certification semantics VERBATIM in
substance: "the rank and pivot selection are heuristic decisions made at
machine precision; the returned kernel entries are certified enclosures
for the solution of the selected r x r subsystem; `resbound` is a rigorous
bound on the residual of the full matrix against the returned basis.  If
the exact matrix represented by the balls has the detected rank, the true
kernel is enclosed; the function cannot prove the rank itself."

## 3. Algorithm (normative)

3.1 Midpoint extraction and scaling.  Build `A0::Matrix{ComplexF64}` from
midpoints (`midpoint(real(a))`, `midpoint(imag(a))`, converted via
`Float64`).  Theta-derived entries can overflow/underflow Float64:
before conversion, compute per-row power-of-two scale factors from the
largest `abs` upper bound in the row (use `arb` magnitude bounds, not
Float64) and scale rows so max magnitudes land near 1; apply the same
scaling to the ball matrix copy used in 3.5 (row scaling does not change
the kernel; column scaling MUST NOT be applied, it does).  If any entry is
non-finite (`!isfinite`), throw `ArgumentError`.

3.2 Pivot stage.  `F = qr(A0, ColumnNorm())` for the pivot ORDER; the
rank decision uses `d = svdvals(A0)` (LAPACK, cheap), since CPQR pivot
magnitudes only track singular values within dimension factors.
With `nullity` given: r = n - nullity.  Otherwise r = number of d[i] >
rtol * d[1] (d[1] > 0 required; a numerically zero matrix returns r = 0
with N = identity).  Pivot columns `piv = F.p[1:r]`, free `free =
F.p[r+1:end]`.

3.3 Row selection.  Choose r rows making the pivot block well-conditioned:
`rows = qr(copy(transpose(A0[:, piv])), ColumnNorm()).p[1:r]`.

3.4 Gap check (only when `nullity === nothing`): if r is 0 < r < n and
`d[r] / d[r+1] < gap`, throw an error naming both values and suggesting
either passing `nullity` or raising precision.  Never return a kernel
across an ambiguous gap silently.

3.5 Certified solve.  `B = A[rows, piv]`, `Rhs = -A[rows, free]` as
`AcbMatrix` (build with `matrix(CC, [...])` comprehensions if fancy
indexing on AcbMatrix is unsupported in the installed Nemo).
`X = solve(B, Rhs; side = :right)` -- this is Nemo's certified acb solve
(the codebase already uses this call form, e.g.
`src/RieSrf/Endomorphisms/HeuristicEndomorphisms.jl:82`).  If it throws
(pivot block not provably invertible at this radius), rethrow as an
informative error: "increase the working precision of A" -- do NOT retry
internally, precision policy belongs to the caller.  Assemble N as in the
API shape.  r == n MUST return an n x 0 matrix and skip the solve.

3.6 Residual certificate.  `Res = A * N` in ball arithmetic (`acb_mat`
multiplication -- the original UNSCALED A).  `resbound` = an `arb` upper
bound of `max_ij abs(Res[i,j])`; use magnitude upper bounds (e.g.
`abs(x)` to `ArbFieldElem` and its upper bound via `ub = ...`; use the
helpers in `src/RieSrf/Numerics/ArbHelpers.jl` if one exists, else add
one there).  This multiply is O(m n (n-r)) in FLINT and MUST stay in
acb_mat; never convert to Julia floats for it.

## 4. Edge cases (all tested)

- r == n (trivial kernel), r == 0 (zero matrix at tolerance), m < n,
  m == 0 or n == 0 (throw ArgumentError), nullity out of range (throw),
  entries with huge exponents (2^±600 scale; the row scaling must make
  the pivot stage work), non-finite entries (throw).

## 5. Tests (`test/RieSrf/NumericalKernel.jl`, wired into the RieSrf tests)

Use fixed RNG seeds.  At `AcbField(1024)`:

1. Known-kernel synthetic: G (m x r) and H (r x n) with small random
   integer entries mapped into CC, A = G*H, m = 40, n = 30, r = 17.
   Check size(N) == (30, 13), r returned == 17, and resbound < 2^-900.
2. Exactness enclosure: build A over QQ first, compute its exact kernel
   with Nemo over QQ, and check every exact kernel vector lies in the
   span: solve the ball system N*c = v_exact ... (simpler equivalent:
   check A_exact * N has all balls containing 0).
3. Wide/huge-nullity case mirroring line 99 of G5ReconstructScript.jl:
   10 x 120 with full row rank; nullity kwarg 110; resbound small.
4. Permutation invariance: kernel of A and of A with shuffled columns
   agree after unshuffling (compare column spans via rank of [N1 N2]
   at Float64 midpoints).
5. Dynamic range: multiply rows of test 1 by 2.0^k for k in -600:150:600;
   same checks pass.
6. Ambiguous gap: a matrix with singular values 1, 1e-6, 1e-7 and
   rtol = 1e-10, no nullity: expect the 3.4 error.
7. Precision failure: test 1 at AcbField(30) with an ill-conditioned
   pivot block scaled to defeat certification if feasible; expect the
   3.5 error (if hard to trigger reliably, test the error path by a
   direct singular B).

## 6. Performance requirements

- No BigFloat anywhere.  No generic-Julia O(n^3) loops over Nemo scalars:
  the only O(n^3) operations are `qr` on ComplexF64 and FLINT-side
  `solve`/`mul`.
- Sanity target: 400 x 500, rank 490, at 1024 bits completes in seconds,
  not minutes, on a laptop.  Add `@vprintln :RieSrf ...` (or the verbose
  macro used elsewhere in RieSrf) reporting r, the gap ratio, and
  resbound.

## 7. Style

Match Hecke house style: 2-space indent, no trailing whitespace,
lowercase_with_underscores, docstring above the function, no `export`.
Check the exact Nemo names available in the installed version before use
(`midpoint`, `radius`, `abs`, `isfinite`, `solve(...; side = :right)`,
`zero_matrix`, `matrix`); where a helper is missing, put it in
`Numerics/ArbHelpers.jl`, not inline.

## 8. Out of scope (do not do here, note as TODO in the PR text)

- Migrating call sites: `Reconstruction/ReconstructG4.jl` lines 19, 36,
  43, 55, 65 (and their duplicates ~603-649) and `manual_kernel` in
  `Reconstruction/G5ReconstructScript.jl` should eventually call this
  function; leave them untouched.
- Orthonormalization of N (callers needing conditioning can Gram-Schmidt
  the small result themselves, at midpoints).
- Any attempt at rigorous rank certification.
