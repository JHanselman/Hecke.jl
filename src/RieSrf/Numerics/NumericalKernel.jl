################################################################################
#
#  numerical_kernel: kernel of a numerically rank-deficient AcbMatrix.
#
#  Spec: src/RieSrf/Reconstruction/NUMERICAL_KERNEL_SPEC.md.  Design: the
#  rank/pivot DECISION is heuristic (ComplexF64 midpoints, pivoted QR); all
#  high-precision arithmetic stays in FLINT acb_mat routines (certified
#  solve, ball residual); the output carries a rigorous residual bound so a
#  wrong heuristic decision is detected, not silently returned.
#
################################################################################

import LinearAlgebra

# ComplexF64 midpoint of x * 2^(-e), scaling done exactly in acb first so
# that entries with exponents beyond Float64 range survive the conversion.
function _mid_c64_scaled(x::AcbFieldElem, e::Int, tmp::AcbFieldElem)
  _acb_mul_2exp!(tmp, x, -e)
  return ComplexF64(_arb_mid_f64(real(tmp)), _arb_mid_f64(imag(tmp)))
end

# x * 2^(-e) as a new element (exact operation).
function _scaled_entry(CC::AcbField, x::AcbFieldElem, e::Int)
  z = CC()
  _acb_mul_2exp!(z, x, -e)
  return z
end

@doc raw"""
    numerical_kernel(A::AcbMatrix; rtol = 1e-10, nullity = nothing, gap = 1e4)
                                          -> AcbMatrix, Int, ArbFieldElem

Kernel of a numerically rank-deficient ball matrix.  Returns `(N, r,
resbound)`: an $n \times (n - r)$ matrix `N` whose columns span the computed
kernel (up to a row permutation of the shape $[X; I]$ -- NOT orthonormal),
the numerical rank `r` used, and `resbound`, an `ArbFieldElem` enclosing
$\max_{ij} |(A N)_{ij}|$, computed in ball arithmetic on the original `A`.

Certification semantics: the rank and pivot selection are heuristic
decisions made at machine precision from midpoints; the returned kernel
entries are certified enclosures for the solution of the selected
$r \times r$ subsystem; `resbound` is a rigorous bound on the residual of
the full matrix against the returned basis.  If the exact matrix
represented by the balls has the detected rank, the true kernel is
enclosed.  The function cannot prove the rank itself: no algorithm can,
since every ball matrix contains full-rank matrices.  Callers must judge
`resbound` against their own tolerance.

Keywords: `rtol` is the relative threshold for the rank decision, ignored
when `nullity` is given; `nullity` forces $r = n - \mathrm{nullity}$ and
skips gap detection; `gap` is the minimum acceptable ratio between the
last kept and first dropped pivot magnitude -- below it the rank is
ambiguous and an error is raised rather than an answer returned.

Raises an error (rather than retrying internally) when the pivot block is
not provably invertible at the working precision; precision policy belongs
to the caller.
"""
function numerical_kernel(A::AcbMatrix; kw...)
  data = _numerical_kernel_data(A; kw...)
  return data.kernel, data.rank, data.residual_bound
end

# numerical_kernel with the pivots of the decision: `pivot_columns` (r
# columns of A, independent if A has rank r; the kernel vectors are 1 at one
# of the other columns and 0 at the rest of them) and `pivot_rows` (r rows of
# A with an invertible pivot block, also chosen for nullity 0).
function _numerical_kernel_data(A::AcbMatrix; rtol::Real = 1e-10,
                                nullity::Union{Int, Nothing} = nothing,
                                gap::Real = 1e4, refine::Bool = false)
  CC = base_ring(A)
  m, n = nrows(A), ncols(A)
  (m == 0 || n == 0) &&
    throw(ArgumentError("numerical_kernel: matrix must have positive dimensions"))
  (0 < rtol < 1) || throw(ArgumentError("numerical_kernel: rtol must be in (0, 1)"))
  gap >= 1 || throw(ArgumentError("numerical_kernel: gap must be >= 1"))
  for i in 1:m, j in 1:n
    isfinite(A[i, j]) ||
      throw(ArgumentError("numerical_kernel: non-finite entry at ($i, $j)"))
  end

  # 3.1: per-row power-of-two exponents from arf midpoint bounds (overflow
  # safe), then the ComplexF64 midpoint matrix of the row-scaled entries.
  # Row scaling does not change the kernel; columns are never scaled.
  ZEROEXP = -(Int64(1) << 60)
  rowe = zeros(Int, m)
  nonzero_columns = [Int[] for _ in 1:m]         # for the residual of sparse A
  for i in 1:m
    e = ZEROEXP
    for j in 1:n
      x = A[i, j]
      iszero(x) || push!(nonzero_columns[i], j)
      e = max(e, _arb_mid_2exp(real(x)), _arb_mid_2exp(imag(x)))
    end
    rowe[i] = e <= ZEROEXP ? 0 : e
  end
  tmp = CC()
  A0 = Matrix{ComplexF64}(undef, m, n)
  for i in 1:m, j in 1:n
    A0[i, j] = _mid_c64_scaled(A[i, j], rowe[i], tmp)
  end

  # 3.2: rank decision on the true singular values of the midpoint matrix
  # (CPQR pivot magnitudes only track them within dimension factors); the
  # pivoted QR supplies the pivot ORDER.
  F = LinearAlgebra.qr(A0, LinearAlgebra.ColumnNorm())
  d = LinearAlgebra.svdvals(A0)
  k = min(m, n)
  if nullity === nothing
    r = (isempty(d) || d[1] == 0) ? 0 : count(>(rtol * d[1]), d)
    # 3.4: never return a kernel across an ambiguous gap silently
    if 0 < r < k && d[r + 1] > 0 && d[r] / d[r + 1] < gap
      error("numerical_kernel: ambiguous rank gap: kept singular value $(d[r]), " *
            "dropped singular value $(d[r + 1]) (ratio $(d[r] / d[r + 1]) < gap = $gap); " *
            "pass nullity explicitly or increase the working precision")
    end
  else
    (0 <= nullity <= n) ||
      throw(ArgumentError("numerical_kernel: nullity must be in [0, $n]"))
    r = n - nullity
    r <= k ||
      throw(ArgumentError("numerical_kernel: nullity = $nullity needs rank " *
                          "$(r) > min(m, n) = $k"))
  end
  piv = collect(F.p[1:r])
  free = collect(F.p[(r + 1):n])

  N = zero_matrix(CC, n, n - r)
  for (c, j) in enumerate(free)
    N[j, c] = one(CC)
  end

  rows = Int[]
  if r > 0
    # 3.3: rows making the pivot block well conditioned
    Fr = LinearAlgebra.qr(Matrix(transpose(A0[:, piv])), LinearAlgebra.ColumnNorm())
    rows = collect(Fr.p[1:r])
  end
  if r > 0 && n - r > 0
    # 3.5: certified solve on the exactly row-scaled ball entries
    B = matrix(CC, AcbFieldElem[_scaled_entry(CC, A[i, j], rowe[i])
                                for i in rows, j in piv])
    Rhs = -matrix(CC, AcbFieldElem[_scaled_entry(CC, A[i, j], rowe[i])
                                   for i in rows, j in free])
    X = refine ? _refined_solve(B, Rhs, A0[rows, piv]) : try
      solve(B, Rhs; side = :right)
    catch err
      error("numerical_kernel: the selected pivot block could not be " *
            "certified invertible at $(precision(CC)) bits; increase the " *
            "working precision of the input (underlying error: " *
            "$(sprint(showerror, err)))")
    end
    for (c, p) in enumerate(piv), t in 1:(n - r)
      N[p, t] = X[c, t]
    end
  end

  # 3.6: rigorous residual bound on the ORIGINAL, unscaled A (acb_mat mul)
  RR = ArbField(precision(CC))
  resbound = zero(RR)
  if n - r > 0 && sum(length, nonzero_columns) < m * n / 4
    # sparse A (e.g. the Fay relations): only the nonzero entries
    for i in 1:m
      entries = [A[i, j] for j in nonzero_columns[i]]
      for t in 1:(n - r)
        s = zero(CC)
        for (x, j) in zip(entries, nonzero_columns[i])
          s += x * N[j, t]
        end
        _arb_max!(resbound, resbound, abs(s))
      end
    end
  elseif n - r > 0
    Res = A * N
    for i in 1:m, j in 1:(n - r)
      _arb_max!(resbound, resbound, abs(Res[i, j]))
    end
  end
  return (kernel = N, rank = r, residual_bound = resbound, pivot_columns = piv, pivot_rows = rows)
end

# Mixed precision iterative refinement for B X = Rhs (B square, rows scaled
# to entries of size at most about 1, B0 its ComplexF64 midpoint matrix): the
# LU decomposition of B0 corrects X with the residual Rhs - B X computed on
# the midpoints at full precision (using the zero entries of B, which are
# many for the Fay relations). Each step gains about -log2(cond(B0) eps) bits,
# for O(n^2) instead of the O(n^3) operations at full precision of the
# certified solve. NOT certified: the radius of X is the heuristic estimate
# sqrt(n) (1 + |X|) rel / sigma_min(B0), rel the largest radius of the
# entries of B and Rhs. Errors if the iteration does not converge.
function _refined_solve(B::AcbMatrix, Rhs::AcbMatrix, B0::Matrix{ComplexF64};
                        max_iterations::Int = 1000)
  CC = base_ring(B)
  prec = precision(CC)
  n, k = nrows(B), ncols(Rhs)
  F = LinearAlgebra.lu(B0; check = false)
  LinearAlgebra.issuccess(F) ||
    error("numerical_kernel: the pivot block is singular at machine precision")
  Bm = map_entries(_acb_mid, B)
  Rm = map_entries(_acb_mid, Rhs)
  nonzeros = [[(j, Bm[i, j]) for j in 1:n if !iszero(Bm[i, j])] for i in 1:n]
  X = zero_matrix(CC, n, k)
  ZERO = -(Int64(1) << 59)
  mid_exponent(z) = max(_arb_mid_2exp(real(z)), _arb_mid_2exp(imag(z)))
  column_exponent(M, c) = max(ZERO, maximum(mid_exponent(M[i, c]) for i in 1:nrows(M)))
  rhs_exponents = [column_exponent(Rm, c) for c in 1:k]
  active = trues(k)
  previous = fill(typemax(Int), k)
  R = zero_matrix(CC, n, k)
  D0 = zeros(ComplexF64, n, k)
  exponents = zeros(Int, k)
  tmp = CC()
  for _ in 1:max_iterations
    for c in 1:k
      active[c] || continue
      for i in 1:n
        s = Rm[i, c]
        for (j, b) in nonzeros[i]
          s -= b * X[j, c]
        end
        R[i, c] = s
      end
      e = column_exponent(R, c)
      scale = max(rhs_exponents[c], column_exponent(X, c))
      # converged, or no progress (the rounding of the residual)
      if e <= ZERO || e <= scale - prec || e > previous[c] - 1
        active[c] = false
        D0[:, c] .= 0
        continue
      end
      previous[c] = e
      exponents[c] = e
      for i in 1:n
        D0[i, c] = _mid_c64_scaled(R[i, c], e, tmp)
      end
    end
    any(active) || break
    D = F \ D0
    for c in 1:k
      active[c] || continue
      for i in 1:n
        z = CC(real(D[i, c]), imag(D[i, c]))
        _acb_mul_2exp!(z, z, exponents[c])
        X[i, c] += z
      end
    end
  end
  for c in 1:k
    scale = max(rhs_exponents[c], column_exponent(X, c))
    previous[c] == typemax(Int) || previous[c] <= scale - div(prec, 2) ||
      error("numerical_kernel: the iterative refinement did not converge (residual " *
            "2^$(previous[c] - scale) relative); the pivot block is too ill conditioned")
  end
  radius64(z) = Float64(Hecke.radius(real(z))) + Float64(Hecke.radius(imag(z)))
  relative = max(maximum(radius64(B[i, j]) for i in 1:n, j in 1:n),
                 maximum(radius64(Rhs[i, c]) for i in 1:n, c in 1:k))
  sigma = minimum(LinearAlgebra.svdvals(B0))
  RR = ArbField(prec)
  for c in 1:k
    largest = maximum(abs(_mid_c64_scaled(X[i, c], 0, tmp)) for i in 1:n)
    err = RR(sqrt(n) * (1 + largest) * relative / sigma)
    for i in 1:n
      _add_error!(X[i, c], err)
    end
  end
  return X
end

# log2 of the size of A N computed on the midpoints, relative per row to the
# largest entry of the row of A times the largest entry of N (an upper bound
# from the exponents; about -precision if the columns of N are kernel
# vectors of the midpoint matrix of A). A diagnostic of the rank decision at
# full precision: the residual bound of numerical_kernel is dominated by the
# radii of A.
function _log2_relative_residual(A::AcbMatrix, N::AcbMatrix)
  ncols(N) == 0 && return -Inf
  mid_exponent(z::AcbFieldElem) = max(_arb_mid_2exp(real(z)), _arb_mid_2exp(imag(z)))
  Am = map_entries(_acb_mid, A)
  R = Am * map_entries(_acb_mid, N)
  eN = maximum(mid_exponent(N[i, j]) for i in 1:nrows(N), j in 1:ncols(N))
  worst = -Inf
  for i in 1:nrows(A)
    eA = maximum(mid_exponent(Am[i, k]) for k in 1:ncols(A))
    eA < -(Int64(1) << 59) && continue                  # zero row
    eR = maximum(mid_exponent(R[i, j]) for j in 1:ncols(R))
    worst = max(worst, Float64(max(eR, -(Int64(1) << 40)) - eA - eN))
  end
  return worst
end

# Convenience for the reconstruction scripts, which build matrices as
# vectors of rows of AcbFieldElem.
function numerical_kernel(rows::Vector{Vector{AcbFieldElem}}; kw...)
  isempty(rows) &&
    throw(ArgumentError("numerical_kernel: matrix must have positive dimensions"))
  CC = parent(rows[1][1])
  n = length(rows[1])
  all(length(v) == n for v in rows) ||
    throw(ArgumentError("numerical_kernel: rows of unequal length"))
  A = matrix(CC, length(rows), n, [x for v in rows for x in v])
  return numerical_kernel(A; kw...)
end
