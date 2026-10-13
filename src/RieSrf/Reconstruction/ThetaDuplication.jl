################################################################################
#
#  ThetaDuplication.jl : all theta constants theta[a, b](0, tau) by the
#  duplication formula, with heuristic choices of the square roots
#
#  theta[a; b](0, tau)^2 = sum_alpha (-1)^(alpha.b) theta[alpha; 0](0, 2 tau)
#                                                  theta[alpha + a; 0](0, 2 tau)
#  (all a, b in {0,1}^g; checked numerically). Starting from 2^h tau, where a
#  few terms of the series suffice, the 2^g constants theta[alpha; 0] are
#  carried down to 2 tau (squares from the formula with b = 0, then square
#  roots), and the last step gives the squares of all 2^(2g) constants at
#  tau. The signs of the square roots come from Float64 sums of the series
#  over the terms within e^-36 of the largest one (Kieffer's "disregarding
#  the correctness requirement for the low-precision approximations"): the
#  arithmetic is in ball arithmetic, but the sign choices and the truncation
#  at 2^h tau are not certified. info.sign_margin is the worst ratio
#  |approximation - chosen root| / |root| (should be far below 1).
#
#  Compare FLINT's acb_theta_all, whose cost in genus >= 6 is dominated by
#  the certified low-precision summation of jets (acb_theta_ql_jet_fd,
#  acb_theta_sum_jet).
#
#  Characteristics: integers 0 .. 2^g - 1, bit k - 1 is entry k; the output
#  is keyed by tuples (a..., b...) as Hecke.thetas.
#
################################################################################

_characteristic_bits(i::Int, g::Int) = [(i >> (k - 1)) & 1 for k in 1:g]

# (a..., b...) is even iff a.b is even
_is_even_characteristic(c) = iseven(sum(c[i] * c[i + div(length(c), 2)] for i in 1:div(length(c), 2)))

# upper triangular R with R^T R = Y (Float64)
function _cholesky_upper64(Y::Matrix{Float64})
  g = size(Y, 1)
  R = zeros(g, g)
  for i in 1:g
    s = Y[i, i] - sum(R[k, i]^2 for k in 1:i-1; init = 0.0)
    @req s > 0 "Im(tau) is not positive definite."
    R[i, i] = sqrt(s)
    for j in i+1:g
      R[i, j] = (Y[i, j] - sum(R[k, i] * R[k, j] for k in 1:i-1; init = 0.0)) / R[i, i]
    end
  end
  return R
end

# the integer vectors n with (n + c)^T Y (n + c) <= bound (R^T R = Y)
function _ellipsoid_points(R::Matrix{Float64}, c::Vector{Float64}, bound::Float64)
  g = length(c)
  points = Vector{Int}[]
  x = zeros(Int, g)
  function search(i::Int, partial::Float64)
    s = sum(R[i, j] * (x[j] + c[j]) for j in i+1:g; init = 0.0) / R[i, i]
    r = sqrt(max(bound - partial, 0.0)) / R[i, i]
    for n in ceil(Int, -s - r - c[i]):floor(Int, -s + r - c[i])
      x[i] = n
      p = partial + (R[i, i] * (n + c[i] + s))^2
      p <= bound || continue
      i == 1 ? push!(points, copy(x)) : search(i - 1, p)
    end
    x[i] = 0
  end
  search(g, 0.0)
  return points
end

_quadratic_value(Y::Matrix{Float64}, v::Vector{Float64}) = sum(v[i] * Y[i, j] * v[j] for i in eachindex(v), j in eachindex(v))

# the points n of the series of theta[a; .] (v = n + a/2) with v^T Y v <=
# min + delta, and the minimum
function _theta_points(R::Matrix{Float64}, Y::Matrix{Float64}, a::Vector{Int}, delta::Float64)
  c = a ./ 2
  start = Float64.(round.(Int, -c)) + c
  candidates = _ellipsoid_points(R, c, _quadratic_value(Y, start) * (1 + 1e-12) + 1e-12)
  qmin = minimum(_quadratic_value(Y, n + c) for n in candidates)
  return _ellipsoid_points(R, c, qmin + delta), qmin
end

# Float64 sums of the series of theta[a; b](0, tau), b in {0,1}^g, scaled by
# exp(pi qmin): sum_m (-1)^(m.b) bins[m] (bins by n mod 2) times i^(a.b)
function _theta_approximations64(X::Matrix{Float64}, Y::Matrix{Float64}, R::Matrix{Float64},
                                 a::Vector{Int}; delta::Float64 = 36 / pi)
  g = length(a)
  points, qmin = _theta_points(R, Y, a, delta)
  bins = zeros(ComplexF64, 2^g)
  for n in points
    v = n + a ./ 2
    m = sum(mod(n[k], 2) << (k - 1) for k in 1:g)
    bins[m + 1] += exp(pi * im * _quadratic_value(X, v) - pi * (_quadratic_value(Y, v) - qmin))
  end
  return _walsh_hadamard!(bins), qmin
end

# (-1)^(popcount(i & j)) transform, in place
function _walsh_hadamard!(v::AbstractVector)
  n = length(v)
  half = 1
  while half < n
    for i in 0:2*half:n-1, j in i:i+half-1
      x, y = v[j + 1], v[j + half + 1]
      v[j + 1], v[j + half + 1] = x + y, x - y
    end
    half *= 2
  end
  return v
end

# theta[alpha; 0](0, tau_h) for all alpha by summation (tau_h with large
# imaginary part: few terms)
function _theta_top_level(tau_h::AcbMatrix, X::Matrix{Float64}, Y::Matrix{Float64}, R::Matrix{Float64},
                          delta::Float64)
  g = nrows(tau_h)
  CC = base_ring(tau_h)
  ipi = onei(CC) * const_pi(CC)
  half = inv(CC(2))
  values = AcbFieldElem[]
  for alpha in 0:2^g-1
    a = _characteristic_bits(alpha, g)
    points, _ = _theta_points(R, Y, a, delta)
    s = zero(CC)
    for n in points
      v = [CC(n[k]) + (a[k] == 1 ? half : zero(CC)) for k in 1:g]
      s += exp(ipi * sum(v[i] * tau_h[i, j] * v[j] for i in 1:g, j in 1:g))
    end
    push!(values, s)
  end
  return values
end

# The root of square with the sign of approximation * exp(-pi qmin) (both
# compared after scaling by exp(pi qmin), the size of the largest term of the
# series); the margin (distance to the chosen root) / (distance to the
# other root); the radius of the root
# relative to exp(-pi qmin). A square that contains 0 (the value vanishes, or
# is lost in cancellation) has the root 0 +- sqrt(|square|): its sign does
# not matter (margin 0), and the ball stays finite (sqrt of a ball around 0
# would cross the branch cut).
function _signed_root(square::AcbFieldElem, approximation::ComplexF64, qmin::Float64)
  CC = parent(square)
  scale = exp(const_pi(CC) * CC(qmin))
  if contains_zero(square)
    a = abs(square)
    root = zero(CC)
    _add_error!(root, sqrt(Hecke.midpoint(a) + Hecke.radius(a)))
    return root, 0.0, _radius64(root * scale)
  end
  root = sqrt(square)
  scaled = _c64(root * scale)
  d_plus, d_minus = abs(approximation - scaled), abs(approximation + scaled)
  # 0: clear choice, 1: no choice possible (the approximation is
  # equidistant from both roots)
  margin = min(d_plus, d_minus) / max(d_plus, d_minus, floatmin(Float64))
  root = d_minus < d_plus ? -root : root
  return root, margin, _radius64(root * scale)
end

# theta[a; b](0, tau) by its series in ball arithmetic, over the terms with
# v^T Y v <= min + delta
function _theta_series(tau::AcbMatrix, R::Matrix{Float64}, Y::Matrix{Float64}, a::Vector{Int},
                       b::Vector{Int}, delta::Float64)
  g = nrows(tau)
  CC = base_ring(tau)
  ipi = onei(CC) * const_pi(CC)
  half = inv(CC(2))
  points, _ = _theta_points(R, Y, a, delta)
  s = zero(CC)
  for n in points
    v = [CC(n[k]) + (a[k] == 1 ? half : zero(CC)) for k in 1:g]
    s += exp(ipi * (sum(v[i] * tau[i, j] * v[j] for i in 1:g, j in 1:g) + sum(v[k] * b[k] for k in 1:g)))
  end
  return s
end

# The sign of root (a square root of theta[a; b](0, tau)^2) from the series in
# ball arithmetic, with the terms down to 1e-16 of |root| (the root is small
# compared with exp(-pi qmin), the largest term); the new margin.
function _resolve_sign(tau::AcbMatrix, R::Matrix{Float64}, Y::Matrix{Float64}, a::Int, b::Int,
                       root::AcbFieldElem, qmin::Float64)
  CC = parent(root)
  g = nrows(tau)
  magnitude = abs(_c64(root * exp(const_pi(CC) * CC(qmin))))
  delta = (36 + log(1 / max(magnitude, 1e-300))) / pi
  # enough precision for the cancellation down to the root, and a margin
  low = min(precision(CC), 64 + ceil(Int, log2(1 / max(magnitude, 1e-300))))
  series = _theta_series(change_base_ring(AcbField(low), tau), R, Y, _characteristic_bits(a, g),
                         _characteristic_bits(b, g), delta)
  series = CC(series)
  d_plus, d_minus = abs(_c64(series - root)), abs(_c64(series + root))
  margin = min(d_plus, d_minus) / max(d_plus, d_minus, floatmin(Float64))
  return d_minus < d_plus ? -root : root, margin
end

# smallest eigenvalue of Y (inverse power iteration; slightly underestimated)
function _smallest_eigenvalue64(Y::Matrix{Float64})
  R = _cholesky_upper64(Y)
  g = size(Y, 1)
  solve(b) = (z = copy(b);
              for i in 1:g; z[i] = (z[i] - sum(R[k, i] * z[k] for k in 1:i-1; init = 0.0)) / R[i, i]; end;
              for i in g:-1:1; z[i] = (z[i] - sum(R[i, k] * z[k] for k in i+1:g; init = 0.0)) / R[i, i]; end;
              z)
  x = ones(g) ./ sqrt(g)
  mu = 0.0
  for _ in 1:100
    y = solve(x)
    mu = sqrt(sum(abs2, y))
    x = y ./ mu
  end
  return 0.9 / mu
end

# One run of the duplication at working precision prec + guard_bits: the
# constants (unrounded), the worst radius of the intermediate values
# theta[alpha; 0](0, 2^k tau) relative to the largest term of their series,
# the worst radius of the final constants relative to the largest one, the
# sign margins.
function _theta_duplication_run(tau::AcbMatrix, squared::Bool, guard_bits::Int)
  g = nrows(tau)
  prec = precision(base_ring(tau))
  CC = AcbField(prec + guard_bits)
  t = change_base_ring(CC, tau)
  t = (t + transpose(t)) * inv(CC(2))
  X = [Float64(Hecke.midpoint(real(t[i, j]))) for i in 1:g, j in 1:g]
  Y = [Float64(Hecke.midpoint(imag(t[i, j]))) for i in 1:g, j in 1:g]
  Y = (Y + transpose(Y)) / 2
  lambda = _smallest_eigenvalue64(Y)
  bits = prec + guard_bits + 10
  h = max(1, ceil(Int, log2(bits * log(2) / (pi * lambda)))) + 1
  scaled(k) = (2.0^k * X, 2.0^k * Y, sqrt(2.0^k) * _cholesky_upper64(Y))
  Xk, Yk, Rk = scaled(h)
  T = _theta_top_level(t * CC(2)^h, Xk, Yk, Rk, bits * log(2) / pi)
  worst_intermediate = 0.0
  worst_radius = 0.0
  for k in h-1:-1:1
    Xk, Yk, Rk = scaled(k)
    S = [sum(T[alpha + 1] * T[xor(alpha, beta) + 1] for alpha in 0:2^g-1) for beta in 0:2^g-1]
    for beta in 0:2^g-1
      bins, qmin = _theta_approximations64(Xk, Yk, Rk, _characteristic_bits(beta, g))
      T[beta + 1], margin, radius = _signed_root(S[beta + 1], bins[1], qmin)
      worst_intermediate = max(worst_intermediate, margin)
      worst_radius = max(worst_radius, radius)
    end
  end
  # T: theta[alpha; 0](0, 2 tau); squares of all constants at tau
  squares = Vector{Vector{AcbFieldElem}}(undef, 2^g)
  for a in 0:2^g-1
    squares[a + 1] = _walsh_hadamard!([T[alpha + 1] * T[xor(alpha, a) + 1] for alpha in 0:2^g-1])
  end
  key(a, b) = Tuple(vcat(_characteristic_bits(a, g), _characteristic_bits(b, g)))
  odd(a, b) = isodd(count_ones(a & b))
  result = Dict{NTuple{2*g, Int}, AcbFieldElem}()
  worst_final = 0.0
  if squared
    for a in 0:2^g-1, b in 0:2^g-1
      result[key(a, b)] = odd(a, b) ? zero(CC) : squares[a + 1][b + 1]
    end
  else
    X0, Y0, R0 = scaled(0)
    undecided = Tuple{Int, Int, AcbFieldElem, Float64}[]
    for a in 0:2^g-1
      bins, qmin = _theta_approximations64(X0, Y0, R0, _characteristic_bits(a, g))
      for b in 0:2^g-1
        if odd(a, b)
          result[key(a, b)] = zero(CC)
          continue
        end
        approximation = bins[b + 1] * im^count_ones(a & b)
        root, margin, _ = _signed_root(squares[a + 1][b + 1], approximation, qmin)
        if margin > 1e-3
          push!(undecided, (a, b, root, qmin))
        else
          worst_final = max(worst_final, margin)
        end
        result[key(a, b)] = root
      end
    end
    # Float64 cannot decide these (constants far below the largest term of
    # their series): their series in ball arithmetic, on all threads
    resolved = Vector{Tuple{AcbFieldElem, Float64}}(undef, length(undecided))
    Threads.@threads for k in eachindex(undecided)
      local a, b, root, qmin = undecided[k]
      resolved[k] = _resolve_sign(t, R0, Y0, a, b, root, qmin)
    end
    for ((a, b, _, _), (root, margin)) in zip(undecided, resolved)
      result[key(a, b)] = root
      worst_final = max(worst_final, margin)
    end
  end
  largest = maximum(abs(_c64(x)) for x in values(result))
  final_radius = maximum(_radius64(x) for x in values(result)) / largest
  return result, (h = h, guard_bits = guard_bits, sign_margin_intermediate = worst_intermediate,
                  sign_margin_final = worst_final, intermediate_scaled_radius = worst_radius,
                  final_relative_radius = final_radius)
end

@doc raw"""
    theta_constants_duplication(tau; squared = false, guard_bits = 4g + 20, max_guard_bits = 8 prec)
        -> Dict, NamedTuple

All theta constants theta[a, b](0, tau) (or their squares), keyed like
Hecke.thetas, by the duplication formula with heuristic sign choices (see
the header of ThetaDuplication.jl). tau should be Siegel reduced.

The duplication loses precision when a value theta[alpha; 0](0, 2^k tau)
is small compared to the terms of its series (its square is a cancelling
sum, and the square root doubles the relative error); a value that vanishes
(it happens: a genus 5 example with theta[alpha; 0](0, 2 tau) = 0) has the
root 0 +- sqrt(radius of the square). The ball arithmetic shows this, so the
computation is repeated with twice the guard bits until the intermediate
values have radius below 2^-prec times the largest term of their series and
the final constants radius below 2^-prec times the largest constant (at most
`max_guard_bits`; a vanishing value needs about prec guard bits). The
duplication runs at the exact midpoint of tau, as Kieffer's code; the
effect of the radius of tau is added at the end from the derivatives of the
series (_add_tau_radius!; an estimate). `info.reliable`: the final
constants have radius at most 2^(-prec/2) of the largest and agree with
independent Float64 sums of their series at tau (margin <= 1e-3; the
margin is (distance to the chosen root) / (distance to the other one)). It can
fail when values theta[alpha; 0](0, 2^k tau) (nearly) vanish: their square
roots lose half of the remaining bits each time (Kieffer's algorithm avoids
this with shifted arguments z != 0); use FLINT then.
Returns the constants (in the field of tau) and `info`: the number of
duplications `h`, the guard bits used, the worst sign margins (intermediate
levels; final constants that are not 0 within their radius; should be far
below 1) and the radii.
"""
function theta_constants_duplication(tau::AcbMatrix; squared::Bool = false,
                                     guard_bits::Int = 4*nrows(tau) + 20,
                                     max_guard_bits::Int = 8 * precision(base_ring(tau)))
  CC0 = base_ring(tau)
  prec = precision(CC0)
  g = nrows(tau)
  target = 2.0^(-prec)
  # at the exact midpoint: the radii are those of the arithmetic only, so
  # guard bits help; the radius of tau is added at the end
  tau_mid = map_entries(_acb_mid, (tau + transpose(tau)) * inv(CC0(2)))
  previous = Inf
  result, info = nothing, nothing
  while true
    result, info = _theta_duplication_run(tau_mid, squared, guard_bits)
    good = info.intermediate_scaled_radius <= target && info.final_relative_radius <= target
    stuck = info.final_relative_radius > previous / 2
    (good || stuck || 2 * guard_bits > max_guard_bits) && break
    previous = info.final_relative_radius
    guard_bits *= 2
  end
  thetas = Dict(k => CC0(v) for (k, v) in result)
  _add_tau_radius!(thetas, tau, tau_mid, squared)
  largest = maximum(abs(_c64(x)) for x in values(thetas))
  final_radius = maximum(_radius64(x) for x in values(thetas)) / largest
  # the final constants are determined to half the precision and agree with
  # the independent Float64 sums of their series at tau (squared: no check)
  reliable = final_radius <= 2.0^(-prec / 2) && (squared || info.sign_margin_final <= 1e-3)
  return thetas, merge(info, (final_relative_radius_with_tau = final_radius, reliable = reliable))
end

# The effect of the radius r of tau (largest over the entries): |d theta[a; b]|
# <= pi r sum_v (sum_k |v_k|)^2 exp(-pi v^T Y v), v in a/2 + Z^g, the same for
# all b (Float64 sum over the terms within e^-36 of the largest, so an
# estimate rather than a bound); for the squares 2 (|theta| + d) d.
function _add_tau_radius!(thetas::Dict, tau::AcbMatrix, tau_mid::AcbMatrix, squared::Bool)
  g = nrows(tau)
  CC = base_ring(tau)
  RR = ArbField(precision(CC))
  r = zero(RR)
  for i in 1:g, j in 1:g
    _arb_max!(r, r, RR(Hecke.radius(real(tau[i, j]))) + RR(Hecke.radius(imag(tau[i, j]))))
  end
  iszero(r) && return thetas
  Y = [Float64(Hecke.midpoint(imag(tau_mid[i, j]))) for i in 1:g, j in 1:g]
  Y = (Y + transpose(Y)) / 2
  R = _cholesky_upper64(Y)
  errors = ArbFieldElem[]
  for a in 0:2^g-1
    bits = _characteristic_bits(a, g)
    points, qmin = _theta_points(R, Y, bits, 36 / pi)
    s = 0.0
    for n in points
      v = n + bits ./ 2
      s += sum(abs, v)^2 * exp(-pi * (_quadratic_value(Y, v) - qmin))
    end
    push!(errors, RR(s) * const_pi(RR) * r * exp(-const_pi(RR) * RR(qmin)))
  end
  for (key, x) in thetas
    _is_even_characteristic(key) || continue
    a = sum(key[k] << (k - 1) for k in 1:g)
    d = errors[a + 1]
    if squared
      m = abs(x)
      d = 2 * (Hecke.midpoint(m) + Hecke.radius(m) + d) * d
    end
    _add_error!(x, d)
  end
  return thetas
end

@doc raw"""
    theta_gradients_single(tau::AcbMatrix, characteristics; parallel = Threads.nthreads() > 1)
                                                     -> Dict{NTuple{2g, Int}, Vector{AcbFieldElem}}

The gradients at z = 0 of theta[a; b](z, tau) for the given characteristics
(tuples or vectors (a..., b...)), each by FLINT's acb_theta_jet for this
characteristic only (certified), on all threads with `parallel`. For when
only a few of the 2^(2g) gradients are needed.
"""
function theta_gradients_single(tau::AcbMatrix, characteristics; parallel::Bool = Threads.nthreads() > 1)
  g = nrows(tau)
  CC = base_ring(tau)
  n = ccall((:acb_theta_jet_nb, Hecke.libflint), Int, (Int, Int), 1, g)
  tuples = zeros(Int, n * g)
  GC.@preserve tuples ccall((:acb_theta_jet_tuples, Hecke.libflint), Nothing, (Ptr{Int}, Int, Int),
                            pointer(tuples), 1, g)
  # the position of d/dz_i in the jet
  position = [findfirst(k -> tuples[g*(k-1)+1:g*k] == [j == i ? 1 : 0 for j in 1:g], 1:n) for i in 1:g]
  function gradient(c)
    th = Hecke.acb_vec(n)
    z = Hecke.acb_vec([zero(CC) for _ in 1:g])
    ab = UInt(evalpoly(2, reverse(collect(c))))
    ccall((:acb_theta_jet, Hecke.libflint), Nothing,
          (Ptr{Hecke.acb_struct}, Ptr{Hecke.acb_struct}, Int, Ref{AcbMatrix}, Int, UInt, Cint, Cint, Int),
          th, z, 1, tau, 1, ab, 0, 0, precision(CC))
    jet = Hecke.array(CC, th, n)
    Hecke.acb_vec_clear(th, n)
    Hecke.acb_vec_clear(z, g)
    return [jet[position[i]] for i in 1:g]
  end
  return _theta_single_map(tau, characteristics, gradient, Vector{AcbFieldElem}; parallel = parallel)
end

# Dict(c => compute(c)) for the characteristics c (as tuples), on all threads
# with `parallel`
function _theta_single_map(tau::AcbMatrix, characteristics, compute, ::Type{V}; parallel::Bool) where V
  g = nrows(tau)
  chars = [Tuple(c) for c in characteristics]
  values = Vector{V}(undef, length(chars))
  if parallel
    Threads.@threads for k in eachindex(chars)
      values[k] = compute(chars[k])
    end
  else
    for (k, c) in enumerate(chars)
      values[k] = compute(c)
    end
  end
  return Dict{NTuple{2*g, Int}, V}(zip(chars, values))
end

@doc raw"""
    theta_constants_single(tau, characteristics; parallel = Threads.nthreads() > 1) -> Dict

The theta constants theta[c](0, tau) for the given characteristics (tuples
(a..., b...)), each by FLINT's acb_theta_one (certified), on all threads with
`parallel`; odd characteristics are 0. For when only part of the 2^(2g)
constants is needed.
"""
function theta_constants_single(tau::AcbMatrix, characteristics; parallel::Bool = Threads.nthreads() > 1)
  g = nrows(tau)
  CC = base_ring(tau)
  z = [zero(CC) for _ in 1:g]
  chars = [Tuple(c) for c in characteristics]
  values = Vector{AcbFieldElem}(undef, length(chars))
  compute(c) = _is_even_characteristic(c) ? Hecke.theta(z, tau, collect(c)) : zero(CC)
  if parallel
    Threads.@threads for k in eachindex(chars)
      local c = chars[k]
      values[k] = compute(c)
    end
  else
    for (k, c) in enumerate(chars)
      values[k] = compute(c)
    end
  end
  return Dict{NTuple{2*g, Int}, AcbFieldElem}(zip(chars, values))
end
