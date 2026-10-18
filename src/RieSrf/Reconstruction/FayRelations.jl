################################################################################
#
#  FayRelations.jl : the gradients of the odd theta functions
#
#  The gradients l_kappa = grad theta[kappa](0) of the odd theta functions
#  satisfy linear relations whose coefficients are products of three even
#  theta constants (Fay; RiemannRelations.jl). Their kernel K (rows: the odd
#  characteristics, g columns) gives the gradients up to a common linear map,
#  i.e. the tangent hyperplanes of the canonical model in some coordinates
#  (odd_theta_gradient_kernel). This is the first step of the reconstruction
#  for g >= 5 (Quadrics.jl), for the curve and for its Prym.
#
#  The relations: for g <= 5 those of a few fixed rho (_fay_rhos), of which a
#  basis is chosen at machine precision; for g = 6, 7 a basis stored in
#  Data/FayRelationsG*.txt (find_fay_relations, save_fay_relations). The
#  kernel of the sparse matrix (n_odd = 2^(g-1)(2^g - 1) columns) is computed
#  in Float64 and refined to the full precision (_sparse_kernel).
#
#  Entry points: odd_theta_gradient_kernel, find_fay_relations,
#  save_fay_relations, load_fay_relations.
#
################################################################################

_default_fay_data_file(g::Int) = joinpath(@__DIR__, "Data", "FayRelationsG$(g).txt")

# The rho of the Fay matrices for genus 5 and its genus 4 Prym (enough for a
# kernel of the right dimension); nothing for other genera.
function _fay_rhos(g::Int)
  F = GF(2)
  g == 5 && return [F.(v) for v in ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 1, 0, 0, 1],
                                     [0, 1, 0, 1, 0, 0, 1, 1, 0, 0], [0, 1, 0, 0, 1, 0, 0, 0, 0, 1],
                                     [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 0, 1, 1, 1, 0, 1, 1, 0, 1],
                                     [1, 0, 1, 0, 1, 1, 0, 1, 0, 1], [0, 0, 1, 0, 1, 1, 0, 1, 0, 0])]
  g == 4 && return [F.(v) for v in ([1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0, 1],
                                     [0, 1, 1, 0, 0, 1, 1, 0], [0, 1, 0, 1, 0, 0, 0, 1],
                                     [1, 1, 1, 1, 1, 1, 1, 1], [1, 0, 1, 1, 0, 1, 0, 1],
                                     [1, 0, 0, 1, 1, 1, 0, 1], [0, 0, 1, 1, 1, 0, 0, 0])]
  return nothing
end

# The nonzero rho in GF(2)^(2g) of weight at most max_weight, by weight
function _fay_rho_candidates(g::Int; max_weight::Int = 3)
  F = GF(2)
  n = 2*g
  vectors = Vector{Int}[]
  for w in 1:min(max_weight, n)
    level = Vector{Int}[]
    function subsets!(v, start, left)
      left == 0 && return push!(level, copy(v))
      for i in start:(n - left + 1)
        v[i] = 1
        subsets!(v, i + 1, left - 1)
        v[i] = 0
      end
    end
    subsets!(zeros(Int, n), 1, w)
    append!(vectors, sort!(level))
  end
  return [F.(v) for v in vectors]
end

# The w in {0,1}^(2g) with <rho, w> = 1 (symplectic), as integer vectors
function _non_orthogonal_doubled(rho::Vector{Int})
  n = length(rho)
  g = div(n, 2)
  result = Vector{Int}[]
  for bits in 0:(2^n - 1)
    w = [(bits >> (n - k)) & 1 for k in 1:n]
    isodd(sum(rho[i] * w[g + i] + w[i] * rho[g + i] for i in 1:g)) && push!(result, w)
  end
  return result
end

# The Fay relations of all rho, of which only n_odd - g + extra are
# evaluated in ball arithmetic: those chosen at machine precision (pivoted QR
# of the row scaled ComplexF64 matrix), the first n_odd - g a basis of the
# relations, the others a check.
function _selected_fay_structure(g::Int, thetas, rhos, odd_indices::Vector{Int}; extra::Int = 2*g)
  LA = LinearAlgebra
  structure = reduce(vcat, [fay_matrix_structure(g, rho) for rho in rhos])
  n_odd = length(odd_indices)
  position = Dict(c => k for (k, c) in enumerate(odd_indices))
  values64 = Dict(k => _c64(v) for (k, v) in thetas)
  A64 = zeros(ComplexF64, length(structure), n_odd)
  for (r, terms) in enumerate(structure), (column, coefficient, c1, c2, c3) in terms
    k = get(position, column, 0)
    k == 0 || (A64[r, k] += coefficient * values64[c1] * values64[c2] * values64[c3])
  end
  for r in axes(A64, 1)
    len = maximum(abs, view(A64, r, :))
    len > 0 && (A64[r, :] ./= len)
  end
  # (LAPACK's pivoted QR can hang on non-finite input)
  @req all(isfinite, A64) "Non-finite Fay relations at machine precision (theta constants with infinite radius?)."
  F = LA.qr(Matrix(transpose(A64)), LA.ColumnNorm())
  keep = sort(F.p[1:min(n_odd - g + extra, length(structure))])
  return structure[keep]
end

# The relations of the structure at the theta constants as sparse rows
# (columns: positions in `columns`, values; empty rows dropped)
function _sparse_fay_rows(structure, thetas, columns::Vector{Int})
  position = Dict(c => k for (k, c) in enumerate(columns))
  rows = Tuple{Vector{Int}, Vector{AcbFieldElem}}[]
  for terms in structure
    entries = Dict{Int, AcbFieldElem}()
    for (column, coefficient, c1, c2, c3) in terms
      k = get(position, column, 0)
      k == 0 && continue
      value = coefficient * (thetas[c1] * thetas[c2] * thetas[c3])
      entries[k] = haskey(entries, k) ? entries[k] + value : value
    end
    filter!(e -> !iszero(e[2]), entries)
    isempty(entries) && continue
    cols = sort!(collect(keys(entries)))
    push!(rows, (cols, [entries[k] for k in cols]))
  end
  return rows
end

# In place, at precision p (FLINT): z += x y and z += x
_acb_addmul!(z::AcbFieldElem, x::AcbFieldElem, y::AcbFieldElem, p::Int) =
  ccall((:acb_addmul, Hecke.libflint), Nothing,
        (Ref{AcbFieldElem}, Ref{AcbFieldElem}, Ref{AcbFieldElem}, Int), z, x, y, p)
_acb_add!(z::AcbFieldElem, x::AcbFieldElem, y::AcbFieldElem, p::Int) =
  ccall((:acb_add, Hecke.libflint), Nothing,
        (Ref{AcbFieldElem}, Ref{AcbFieldElem}, Ref{AcbFieldElem}, Int), z, x, y, p)

# The kernel (dimension `nullity`) of the sparse matrix with the given rows
# ((columns, values)) and n columns:
#  - rows and columns are scaled by powers of 2 (exact; two rounds);
#  - at machine precision (midpoints): pivot columns from the pivoted QR of A0
#    (its R diagonal checks the rank gap; in BigFloat if Float64 does not
#    decide, for n <= big_limit), pivot rows from the pivoted QR of the
#    transpose of the pivot columns; for n > dense_limit the kernel by
#    inverse iteration with the unpivoted QR instead;
#  - the kernel [X; I] at full precision by iterative refinement of
#    B X = -A[rows, free] (B = A[rows, pivots]) with the Float64 (or BigFloat)
#    factorization of B0; the residuals are computed at the precision they
#    need (the bits reached so far + 128);
#  - its radius estimated from sigma_min(B0) (inverse iteration).
# Returns K (n x nullity) and log2 of the relative residual of the scaled
# matrix on the midpoints of all rows.
function _sparse_kernel(rows, n::Int, nullity::Int; max_iterations::Int = 300, verbose::Bool = false,
                        basis_rows::Bool = false, dense_limit::Int = 4000, big_limit::Int = 600)
  LA = LinearAlgebra
  start_time = time()
  elapsed() = round(time() - start_time, digits = 1)
  CC = parent(rows[1][2][1])
  prec = precision(CC)
  m = length(rows)
  r = n - nullity
  @req m >= r "Only $m relations for rank $r."
  ZERO = -(Int64(1) << 59)
  mid_exponent(z) = max(ZERO, _arb_mid_2exp(real(z)), _arb_mid_2exp(imag(z)))
  tmp = CC()
  # exact scaling of rows and columns by powers of 2
  scaled = [[_scaled_entry(CC, v, 0) for v in vals] for (_, vals) in rows]
  column_shift = zeros(Int, n)             # A' = A_rows diag(2^-column_shift)
  for _ in 1:2
    for vals in scaled
      e = maximum(mid_exponent, vals)
      e > ZERO && foreach(v -> _acb_mul_2exp!(v, v, -e), vals)
    end
    ce = fill(ZERO, n)
    for ((cols, _), vals) in zip(rows, scaled), (j, v) in zip(cols, vals)
      ce[j] = max(ce[j], mid_exponent(v))
    end
    ce[ce .== ZERO] .= 0
    for ((cols, _), vals) in zip(rows, scaled), (j, v) in zip(cols, vals)
      _acb_mul_2exp!(v, v, -ce[j])
    end
    column_shift .+= ce
  end
  mids = [map(_acb_mid, vals) for vals in scaled]
  wide = false                             # BigFloat pivots (see below)
  A0 = zeros(ComplexF64, m, n)
  for (i, (cols, _)) in enumerate(rows), (k, j) in enumerate(cols)
    A0[i, j] = _mid_c64_scaled(mids[i][k], 0, tmp)
  end
  @req all(isfinite, A0) "Non-finite Fay relations at machine precision (theta constants with infinite radius?)."
  verbose && println("A0 built and scaled ($m x $n; column scales 2^$(-maximum(column_shift)) to 2^$(-minimum(column_shift))) [$(elapsed()) s]")
  if n > dense_limit
    # large n (pivoted QRs too slow: BLAS 2). The Float64 kernel from the
    # unpivoted (BLAS 3) Householder QR A0 = Q R: kernel(A0) = kernel(R), by
    # subspace inverse iteration with R^H R (triangular solves); the free
    # columns where it is well conditioned (pivoted QR of its g x n
    # transpose, cheap). The pivot columns A0[:, piv] (all rows) then have
    # full rank r and are well conditioned: corrections by least squares with
    # their QR, residuals on all rows. (A square block of r chosen rows can
    # be far worse conditioned than all rows together: the stored basis rows
    # gave sigma_min 1e-17, all rows 7e-12 in genus 7.)
    Fa = LA.qr(A0)
    Ra = Matrix(Fa.R)
    da = abs.(LA.diag(Ra))
    floor_value = eps() * maximum(da)
    for i in 1:n
      abs(Ra[i, i]) < floor_value && (Ra[i, i] = floor_value)
    end
    T = LA.UpperTriangular(Ra)
    Y = Matrix(LA.qr(randn(ComplexF64, n, nullity)).Q)
    for _ in 1:4
      Y = Matrix(LA.qr(T \ (T' \ Y)).Q)
    end
    kernel_residual = maximum(abs, A0 * Y)
    verbose && println("kernel QR done: R diagonal from $(maximum(da)) to $(minimum(da)); Float64 kernel residual $kernel_residual [$(elapsed()) s]")
    free = sort(LA.qr(Matrix(transpose(Y)), LA.ColumnNorm()).p[1:nullity])
    piv = setdiff(1:n, free)
    prows = collect(1:m)
    Fp = LA.qr(A0[:, piv])
    Tp = LA.UpperTriangular(Matrix(Fp.R))
    solve_correction = D -> Fp \ D
    inverse_normal = v -> Tp \ (Tp' \ v)
  else
    F = LA.qr(A0, LA.ColumnNorm())
    d = abs.(LA.diag(F.R))
    verbose && println("column QR done: R diagonal $(d[1]) first, $(d[r]) at $r, $(r < min(m, n) ? d[r + 1] : 0.0) after [$(elapsed()) s]")
    clear64 = d[r] > 1e-12 * d[1] && (r == min(m, n) || d[r + 1] < 1e-3 * d[r])
    if clear64
      piv = F.p[1:r]
      free = sort(F.p[r + 1:n])
      prows = LA.qr(Matrix(transpose(A0[:, piv])), LA.ColumnNorm()).p[1:r]
      F0 = LA.lu(A0[prows, piv]; check = false)
      @req LA.issuccess(F0) "The pivot block of the Fay relations is singular at machine precision."
      solve_correction = D -> F0 \ D
      inverse_normal = v -> F0' \ (F0 \ v)
    else
      # not decidable in Float64 (a dynamic range beyond 2^-53, e.g. theta
      # constants near the boundary of the Jacobian locus): the same choices
      # in BigFloat (its default precision), slower (generic pivoted QR);
      # the corrections of the refinement are solved there too
      # (generic BigFloat linear algebra is O(m n^2) without BLAS: hours for
      # the 2016 odd characteristics of genus 6, so only for small n)
      @req n <= big_limit "The Fay relations do not have a clear rank $r at machine precision (R diagonal $(d[r]), $(r < min(m, n) ? d[r + 1] : 0.0)), and n = $n > big_limit = $big_limit is too large for the BigFloat fallback."
      wide = true
      big_bits = precision(BigFloat)
      AB = zeros(Complex{BigFloat}, m, n)
      for (i, (cols, _)) in enumerate(rows), (k, j) in enumerate(cols)
        AB[i, j] = Complex(BigFloat(real(mids[i][k])), BigFloat(imag(mids[i][k])))
      end
      FB = LA.qr(AB, LA.ColumnNorm())
      dB = abs.(LA.diag(FB.R))
      verbose && println("column QR at $big_bits bits: R diagonal $(Float64(dB[r] / dB[1])) at $r, ",
                         "$(r < min(m, n) ? Float64(dB[r + 1] / dB[1]) : 0.0) after (relative) [$(elapsed()) s]")
      @req dB[r] > big(2.0)^(40 - big_bits) * dB[1] && (r == min(m, n) || dB[r + 1] < big(1e-3) * dB[r]) "The Fay relations do not have a clear rank $r at machine precision (R diagonal $(d[r]), $(r < min(m, n) ? d[r + 1] : 0.0)), nor at $big_bits bits (relative $(Float64(dB[r] / dB[1])), $(r < min(m, n) ? Float64(dB[r + 1] / dB[1]) : 0.0))."
      piv = FB.p[1:r]
      free = sort(FB.p[r + 1:n])
      prows = LA.qr(Matrix(transpose(AB[:, piv])), LA.ColumnNorm()).p[1:r]
      FB0 = LA.lu(AB[prows, piv]; check = false)
      @req LA.issuccess(FB0) "The pivot block of the Fay relations is singular at $big_bits bits."
      solve_correction = D -> ComplexF64.(FB0 \ Complex{BigFloat}.(D))
      inverse_normal = v -> ComplexF64.(FB0' \ (FB0 \ Complex{BigFloat}.(v)))
    end
  end
  nres = length(prows)
  # sigma_min of the pivot columns by inverse iteration (B^H B)^-1
  v = ones(ComplexF64, r) / sqrt(r)
  growth = 1.0
  for _ in 1:20
    w = inverse_normal(v)
    growth = LA.norm(w)
    v = w / growth
  end
  sigma = 1 / sqrt(growth)
  verbose && println("pivots chosen, sigma_min of the pivot columns about $sigma [$(elapsed()) s]")
  @req sigma > (wide ? 2.0^(60 - precision(BigFloat)) : 1e-14) "The Fay relations have rank < $r at machine precision (sigma_min of the pivot columns $sigma)."
  # the Float64 residual of the kernel estimate on all rows: rank check
  Xf = -solve_correction(A0[prows, free])
  Kf = zeros(ComplexF64, n, nullity)
  Kf[piv, :] = Xf
  for (c, j) in enumerate(free)
    Kf[j, c] = 1
  end
  residual64 = maximum(abs, A0 * Kf) / maximum(abs, Kf)
  @req residual64 < 1e-6 "The Fay relations have rank > $r at machine precision (relative residual $residual64)."
  verbose && println("Float64 kernel residual $residual64; refining [$(elapsed()) s]")
  # refinement of X (columns X[c], length r) with B X = -A[prows, free]
  pivot_position = Dict(j => k for (k, j) in enumerate(piv))
  free_position = Dict(j => c for (c, j) in enumerate(free))
  pivot_terms = [[(pivot_position[j], a) for (j, a) in zip(rows[i][1], mids[i]) if haskey(pivot_position, j)] for i in prows]
  free_terms = [[(free_position[j], a) for (j, a) in zip(rows[i][1], mids[i]) if haskey(free_position, j)] for i in prows]
  X = [[CC() for _ in 1:r] for _ in 1:nullity]
  R = [[CC() for _ in 1:nres] for _ in 1:nullity]
  vector_exponent(V) = maximum(mid_exponent, V)
  rhs_exponents = zeros(Int, nullity)
  bits = zeros(Int, nullity)                   # bits of the residual reached
  active = trues(nullity)
  previous = fill(typemax(Int), nullity)
  exponents = zeros(Int, nullity)
  # the right hand sides of the corrections: in BigFloat with the BigFloat
  # pivots (rounding them to Float64 would lose everything for a pivot block
  # with condition number beyond 2^53)
  D0 = wide ? zeros(Complex{BigFloat}, nres, nullity) : zeros(ComplexF64, nres, nullity)
  scaled_tmp = CC()
  for iteration in 1:max_iterations
    for c in 1:nullity
      active[c] || continue
      working = min(prec + 32, bits[c] + 128)
      Xc, Rc = X[c], R[c]
      for k in 1:nres
        s = Rc[k]
        ccall((:acb_zero, Hecke.libflint), Nothing, (Ref{AcbFieldElem},), s)
        for (cf, a) in free_terms[k]
          cf == c && _acb_add!(s, s, a, working)
        end
        for (p, a) in pivot_terms[k]
          _acb_addmul!(s, a, Xc[p], working)
        end
      end
      e = vector_exponent(Rc)
      iteration == 1 && (rhs_exponents[c] = e)
      scale = max(rhs_exponents[c], vector_exponent(Xc))
      bits[c] = scale - e
      verbose && c == 1 && println("iteration $iteration: residual 2^$(e - scale) at $working bits [$(elapsed()) s]")
      # converged, or stagnating (less than 2 bits per step)
      if e <= ZERO || e <= scale - prec || e > previous[c] - 2
        active[c] = false
        D0[:, c] .= 0
        continue
      end
      previous[c] = e
      exponents[c] = e
      for k in 1:nres
        if wide
          _acb_mul_2exp!(scaled_tmp, Rc[k], -e)
          D0[k, c] = -Complex(BigFloat(Hecke.midpoint(real(scaled_tmp))), BigFloat(Hecke.midpoint(imag(scaled_tmp))))
        else
          D0[k, c] = -_mid_c64_scaled(Rc[k], e, tmp)
        end
      end
    end
    any(active) || break
    D = solve_correction(D0)
    for c in 1:nullity
      active[c] || continue
      for k in 1:r
        z = CC(real(D[k, c]), imag(D[k, c]))
        _acb_mul_2exp!(z, z, exponents[c])
        X[c][k] = X[c][k] + z
      end
    end
  end
  for c in 1:nullity
    scale = max(rhs_exponents[c], vector_exponent(X[c]))
    previous[c] == typemax(Int) || previous[c] <= scale - div(prec, 2) ||
      error("The iterative refinement did not converge (residual 2^$(previous[c] - scale) relative).")
  end
  verbose && println("refined [$(elapsed()) s]")
  # radius estimate
  radius64(z) = Float64(Hecke.radius(real(z))) + Float64(Hecke.radius(imag(z)))
  relative = maximum(maximum(radius64, vals) for vals in scaled)
  RR = ArbField(prec)
  for c in 1:nullity
    largest = maximum(abs(_c64(x)) for x in X[c])
    err = RR(sqrt(r) * (1 + largest) * relative / sigma)
    foreach(x -> _add_error!(x, err), X[c])
  end
  # the kernel of the scaled matrix
  Ks = zero_matrix(CC, n, nullity)
  for (k, j) in enumerate(piv), c in 1:nullity
    Ks[j, c] = X[c][k]
  end
  for (c, j) in enumerate(free)
    Ks[j, c] = one(CC)
  end
  # log2 relative residual on the midpoints of all rows (scaled to 1)
  Kmid = [[_acb_mid(Ks[j, c]) for j in 1:n] for c in 1:nullity]
  eN = maximum(maximum(mid_exponent, Kc) for Kc in Kmid)
  worst = -Inf
  for (i, (cols, _)) in enumerate(rows), c in 1:nullity
    s = zero(CC)
    for (j, a) in zip(cols, mids[i])
      _acb_addmul!(s, a, Kmid[c][j], prec)
    end
    es = mid_exponent(s)
    es > ZERO && (worst = max(worst, Float64(es - eN)))
  end
  # back to the kernel of A: K = diag(2^-column_shift) Ks
  K = zero_matrix(CC, n, nullity)
  for j in 1:n, c in 1:nullity
    x = Ks[j, c]
    _acb_mul_2exp!(x, x, -column_shift[j])
    K[j, c] = x
  end
  return K, worst
end

@doc raw"""
    odd_theta_gradient_kernel(g, thetas; rhos = nothing, relations = nothing) -> AcbMatrix, Float64

The kernel K of Fay's linear relations between the gradients of the odd
theta functions at 0 (rows: the odd characteristics in the order of
odd_theta_characteristics(g), g columns), i.e. the gradients up to a common
linear map, and log2 of its relative residual on the midpoints. `thetas`:
the theta constants of genus g (with signs). The relations, in this order of
preference: `relations` (a list of find_fay_relations or a file of
save_fay_relations); those of `rhos` or of _fay_rhos(g) (genus 4 and 5); the
file _default_fay_data_file(g) if it exists (genus 6 and 7);
find_fay_relations for these theta constants (slow for g >= 6).
"""
function odd_theta_gradient_kernel(g::Int, thetas; rhos = nothing, relations = nothing, verbose::Bool = false)
  odd_indices = char_to_index.(collect.(odd_theta_characteristics(g)))
  structure, stored_relations = _fay_structure(g, thetas, odd_indices; rhos = rhos, relations = relations)
  verbose && println("structure: $(length(structure)) relations")
  rows = _sparse_fay_rows(structure, thetas, odd_indices)
  verbose && println("sparse rows: $(length(rows)), $(sum(r -> length(r[1]), rows)) entries")
  # stored relations (find_fay_relations): the first n_odd - g are a basis
  stored = stored_relations && length(rows) == length(structure)
  return _sparse_kernel(rows, length(odd_indices), g; verbose = verbose, basis_rows = stored)
end

# The Fay relations used by odd_theta_gradient_kernel and whether they are
# stored ones
function _fay_structure(g::Int, thetas, odd_indices::Vector{Int}; rhos = nothing, relations = nothing)
  rhos === nothing && relations === nothing && (rhos = _fay_rhos(g))
  if relations === nothing && rhos === nothing
    file = _default_fay_data_file(g)
    if isfile(file)
      relations = file
    else
      @info "No Fay relations for genus $g (_default_fay_data_file($g)); searching them for this curve. Save the result of find_fay_relations to skip this."
      relations = find_fay_relations(g, thetas)
    end
  end
  relations === nothing && return _selected_fay_structure(g, thetas, rhos, odd_indices), false
  relations isa AbstractString && (relations = load_fay_relations(relations))
  setup = _fay_setup(g)
  return [_fay_relation_structure(g, w, sigma, setup) for (w, sigma) in relations], true
end

@doc raw"""
    find_fay_relations(g, thetas; extra = 2g, chunk = 256, tolerance = 1e-6, verbose = false)
        -> Vector{Tuple{Vector{Int}, Vector{Int}}}

A basis of Fay's relations between the gradients of the odd theta functions
(n_odd - g of them) and `extra` more as a check, as pairs (w, rho) of
characteristics (bit vectors). Chosen at machine precision from the theta
constants `thetas` of a generic curve of genus g: the relations of the rho of
small weight are kept when they are independent of the ones kept before.
Which relations are independent does not depend on the (generic) curve: save
the result with save_fay_relations (to _default_fay_data_file(g) to make it
the default).
"""
function find_fay_relations(g::Int, thetas; extra::Int = 2*g, chunk::Int = 256,
                            tolerance::Float64 = 1e-6, verbose::Bool = false)
  LA = LinearAlgebra
  odd_indices = char_to_index.(collect.(odd_theta_characteristics(g)))
  n = length(odd_indices)
  target = n - g
  position = Dict(c => k for (k, c) in enumerate(odd_indices))
  values64 = Dict(k => _c64(v) for (k, v) in thetas)
  setup = _fay_setup(g)
  # the relation as a normalized Float64 vector
  function relation_vector(w, sigma)
    v = zeros(ComplexF64, n)
    for (column, coefficient, c1, c2, c3) in _fay_relation_structure(g, w, sigma, setup)
      k = get(position, column, 0)
      k == 0 || (v[k] += coefficient * values64[c1] * values64[c2] * values64[c3])
    end
    len = LA.norm(v)
    len > 0 && (v ./= len)
    return v
  end
  # proportional relations (different (w, rho), the same row up to a factor)
  # are skipped
  seen = Set{Any}()
  function signature(v)
    j = findfirst(!iszero, v)
    j === nothing && return nothing
    u = v ./ v[j]
    return Tuple((k, round(real(u[k]), sigdigits = 10), round(imag(u[k]), sigdigits = 10)) for k in findall(!iszero, u))
  end
  U = zeros(ComplexF64, n, 0)                 # orthonormal basis of the span
  selected = Tuple{Vector{Int}, Vector{Int}}[]
  last_block = Tuple{Vector{Int}, Vector{Int}}[]
  last_rest = Int[]
  for rho in _fay_rho_candidates(g)
    sigma = Int.(lift.(Ref(ZZ), rho))
    ws = _non_orthogonal_doubled(sigma)
    for start in 1:chunk:length(ws)
      block = Tuple{Vector{Int}, Vector{Int}}[]
      columns = Vector{ComplexF64}[]
      for w in ws[start:min(start + chunk - 1, end)]
        v = relation_vector(w, sigma)
        key = signature(v)
        (key === nothing || key in seen) && continue
        push!(seen, key)
        push!(block, (w, sigma))
        push!(columns, v)
      end
      isempty(block) && continue
      V = reduce(hcat, columns)
      @req all(isfinite, V) "Non-finite Fay relations at machine precision (theta constants with infinite radius?)."
      W = V - U * (U' * V)
      W -= U * (U' * W)                       # twice (classical Gram-Schmidt)
      F = LA.qr(W, LA.ColumnNorm())
      new = min(count(>(tolerance), abs.(LA.diag(F.R))), target - size(U, 2))
      if new > 0
        Q = Matrix(F.Q)[:, 1:new]
        Q -= U * (U' * Q)
        Q -= U * (U' * Q)
        U = hcat(U, Matrix(LA.qr(Q).Q)[:, 1:new])
        append!(selected, [block[j] for j in F.p[1:new]])
      end
      last_block, last_rest = block, F.p[new + 1:end]
      size(U, 2) < target && continue
      # verification: the LU (partial pivoting) of the selected relations,
      # as columns; (nearly) zero pivots mark relations that depend on the
      # ones before them (lost orthogonality of U): drop them, rebuild U
      M = reduce(hcat, [relation_vector(w, s) for (w, s) in selected])
      Ft = LA.lu(M; check = false)
      du = abs.(LA.diag(Ft.U))
      bad = findall(<(1e-10 * maximum(du)), du)
      verbose && println("rank $(size(U, 2)) reached; verification: $(length(bad)) dependent relations")
      if isempty(bad)
        length(last_rest) >= extra || @info "Only $(length(last_rest)) check relations (asked for $extra)."
        append!(selected, [last_block[j] for j in last_rest[1:min(extra, end)]])
        return selected
      end
      deleteat!(selected, bad)
      U = Matrix(LA.qr(reduce(hcat, [relation_vector(w, s) for (w, s) in selected])).Q)[:, 1:length(selected)]
    end
    verbose && println("rho = $sigma: rank $(size(U, 2)) of $target")
  end
  error("The Fay relations of all rho have rank $(size(U, 2)), less than $target.")
end

@doc raw"""
    save_fay_relations(file, relations)

Writes the relations (w, rho) of find_fay_relations to `file`, one per line
as two strings of 2g bits.
"""
function save_fay_relations(file::AbstractString, relations)
  open(file, "w") do io
    g = div(length(relations[1][1]), 2)
    println(io, "# Fay relations of genus $g (load_fay_relations): one relation (w, rho) per line,")
    println(io, "# w and rho as $(2*g) bits each.")
    for (w, rho) in relations
      println(io, join(string.(w)), " ", join(string.(rho)))
    end
  end
  return nothing
end

@doc raw"""
    load_fay_relations(file) -> Vector{Tuple{Vector{Int}, Vector{Int}}}

The relations written by save_fay_relations. The stored relations of genus 6
and 7 are in the folder Data next to this file.
"""
function load_fay_relations(file::AbstractString)
  relations = Tuple{Vector{Int}, Vector{Int}}[]
  for line in eachline(file)
    (isempty(line) || startswith(line, "#")) && continue
    w, rho = split(line)
    push!(relations, ([parse(Int, c) for c in w], [parse(Int, c) for c in rho]))
  end
  return relations
end
