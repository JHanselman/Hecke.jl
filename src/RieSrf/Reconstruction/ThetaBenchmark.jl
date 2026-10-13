################################################################################
#
#  ThetaBenchmark.jl : where does the time of the theta constants go?
#
#  Times Hecke.thetas (acb_theta_all) for one period matrix
#    * at several precisions (quasi-linear in the precision if the
#      duplication algorithm dominates, faster growth if the summation does),
#    * on the matrix reduced by FLINT (acb_siegel_reduce, LLL based) and on
#      the matrix reduced with HKZ bases of Im(tau) (hkz_siegel_reduction
#      below; Kieffer's paper mentions HKZ as the better reduction),
#    * with 1 and with several FLINT threads (does acb_theta use them?),
#  and once with squared = true and once theta_jets of order 1 (relative to
#  the plain constants). The quality of the reductions: the smallest
#  eigenvalue and the smallest diagonal entry of Im(tau), max |Re(tau)|.
#
#  Usage (in Main, after using Hecke or Oscar):
#    include("tools/ThetaBenchmark.jl")
#    R, (x, y) = polynomial_ring(QQ, [:x, :y])
#    f = 17*x^3*y^4 + 10*x^3*y^2 - 7*x^3 + 20*x^2*y^4 + 10*x^2*y^3 - 10*x*y^4 - 7*x*y - 15*x - 7*y^3 + 6*y
#    tau = small_period_matrix(riemann_surface(f, 600))      # genus 6
#    results = theta_benchmark(tau)
#
#  A development tool, not part of Hecke.
#
################################################################################

import LinearAlgebra
import Profile

################################################################################
#  HKZ reduction of Im(tau)
################################################################################

# A shortest nonzero integer vector of the positive definite Gram matrix G
# (Fincke-Pohst enumeration with the Cholesky factor; Float64, small n).
function _shortest_vector(G::Matrix{Float64})
  n = size(G, 1)
  R = LinearAlgebra.cholesky(LinearAlgebra.Symmetric(G)).U
  i0 = argmin([G[i, i] for i in 1:n])
  best = G[i0, i0] * (1 + 1e-12)
  best_x = [i == i0 ? 1 : 0 for i in 1:n]
  x = zeros(Int, n)
  # x[i+1..n] fixed with partial length `partial`; enumerate x[i]
  function search(i::Int, partial::Float64)
    center = -sum((R[i, j] / R[i, i]) * x[j] for j in i+1:n; init = 0.0)
    radius = sqrt(max(best - partial, 0.0)) / R[i, i]
    for xi in ceil(Int, center - radius):floor(Int, center + radius)
      x[i] = xi
      p = partial + R[i, i]^2 * (xi - center)^2
      p < best || continue
      if i > 1
        search(i - 1, p)
      elseif any(!iszero, x)
        best, best_x = p, copy(x)
      end
    end
    x[i] = 0
  end
  search(n, 0.0)
  return best_x
end

# U (unimodular, columns: the new basis) such that U^T Y U has an HKZ basis:
# column k is a shortest vector of the projection of the lattice spanned by
# columns k..g orthogonally to columns 1..k-1.
function _hkz_basis(Y::Matrix{Float64})
  g = size(Y, 1)
  U = identity_matrix(ZZ, g)
  for k in 1:g-1
    Uf = Float64.(Matrix(U))
    G = transpose(Uf) * Y * Uf
    S = k == 1 ? G : G[k:g, k:g] - G[k:g, 1:k-1] * (G[1:k-1, 1:k-1] \ G[1:k-1, k:g])
    c = _shortest_vector((S + transpose(S)) / 2)
    _, T = hnf_with_transform(matrix(ZZ, length(c), 1, c))   # T c = +-e_1
    W = inv(T)                                               # first column +-c
    U = hcat(U[:, 1:k-1], U[:, k:g] * W)
  end
  return U
end

_mid64(z) = Float64(Hecke.midpoint(z))

function _block_matrix(A::ZZMatrix, B::ZZMatrix, C::ZZMatrix, D::ZZMatrix)
  return vcat(hcat(A, B), hcat(C, D))
end

@doc raw"""
    hkz_siegel_reduction(tau; max_iterations = 100) -> ZZMatrix, AcbMatrix

Siegel reduction with HKZ bases: repeat (1) U^T tau U with an HKZ basis U
of Im(tau), (2) tau - round(Re(tau)), (3) the quasi-inversion
tau_11 -> -1/tau_11 if |tau_11| < 1, until |tau_11| >= 1. Returns the
symplectic matrix T and T(tau) (as Hecke.siegel_reduction).
"""
function hkz_siegel_reduction(tau::AcbMatrix; max_iterations::Int = 100)
  g = nrows(tau)
  I, Z = identity_matrix(ZZ, g), zero_matrix(ZZ, g, g)
  T = identity_matrix(ZZ, 2*g)
  for _ in 1:max_iterations
    t = Hecke.siegel_transform(T, tau)
    Y = [_mid64(imag(t[i, j])) for i in 1:g, j in 1:g]
    U = _hkz_basis((Y + transpose(Y)) / 2)
    T = _block_matrix(transpose(U), Z, Z, inv(U)) * T
    t = Hecke.siegel_transform(T, tau)
    B = zero_matrix(ZZ, g, g)
    for i in 1:g, j in i:g
      B[i, j] = B[j, i] = -round(Int, _mid64(real(t[i, j])))
    end
    T = _block_matrix(I, B, Z, I) * T
    t = Hecke.siegel_transform(T, tau)
    abs(Complex(_mid64(real(t[1, 1])), _mid64(imag(t[1, 1])))) >= 1 - 1e-12 && break
    A = identity_matrix(ZZ, g)
    A[1, 1] = 0
    E = zero_matrix(ZZ, g, g)
    E[1, 1] = 1
    T = _block_matrix(A, -E, E, A) * T
  end
  t = Hecke.siegel_transform(T, tau)
  return T, (t + transpose(t)) * inv(base_ring(t)(2))
end

# smallest eigenvalue and smallest diagonal entry of Im(tau), max |Re(tau)|
function reduction_quality(tau::AcbMatrix)
  g = nrows(tau)
  Y = [_mid64(imag(tau[i, j])) for i in 1:g, j in 1:g]
  X = [_mid64(real(tau[i, j])) for i in 1:g, j in 1:g]
  return (min_eigenvalue = minimum(LinearAlgebra.eigvals(LinearAlgebra.Symmetric((Y + transpose(Y)) / 2))),
          min_diagonal = minimum(Y[i, i] for i in 1:g), max_real = maximum(abs, X))
end

################################################################################
#  The benchmark
################################################################################

_set_flint_threads(n::Int) = ccall((:flint_set_num_threads, Nemo.libflint), Nothing, (Cint,), n)
_get_flint_threads() = Int(ccall((:flint_get_num_threads, Nemo.libflint), Cint, ()))

function _time_thetas(tau::AcbMatrix, prec::Int; squared::Bool = false)
  t = change_base_ring(AcbField(prec), tau)
  CC = base_ring(t)
  z = [zero(CC) for _ in 1:nrows(t)]
  return @elapsed Hecke.thetas(z, t; squared = squared)
end

@doc raw"""
    theta_benchmark(tau; precisions = [128, 256, 512], threads = [1, Sys.CPU_THREADS],
                    squared_precision = 256, jets_precision = 256) -> Vector{NamedTuple}

Times Hecke.thetas for tau reduced by FLINT and by hkz_siegel_reduction, at
the given precisions and FLINT thread counts (printed as it goes); then
squared = true and theta_jets of order 1 once each. tau must have at least the
largest precision.
"""
function theta_benchmark(tau::AcbMatrix; precisions = [128, 256, 512], threads = [1, Sys.CPU_THREADS],
                         squared_precision::Int = 256, jets_precision::Int = 256)
  g = nrows(tau)
  @req precision(base_ring(tau)) >= maximum(precisions) "tau needs at least $(maximum(precisions)) bits."
  old_threads = _get_flint_threads()
  _, tau_flint = Hecke.siegel_reduction(tau)
  _, tau_hkz = hkz_siegel_reduction(tau)
  variants = [(:input, tau), (:flint, tau_flint), (:hkz, tau_hkz)]
  println("genus $g")
  for (name, t) in variants
    println(rpad(string(name), 8), reduction_quality(t))
  end
  _time_thetas(tau_flint, 64)                           # compilation
  results = NamedTuple[]
  println(rpad("variant", 8), lpad("threads", 8), lpad("prec", 6), lpad("seconds", 10))
  for n in threads
    _set_flint_threads(n)
    for (name, t) in variants[2:3], prec in precisions
      s = _time_thetas(t, prec)
      println(rpad(string(name), 8), lpad(n, 8), lpad(prec, 6), lpad(round(s, digits = 2), 10))
      push!(results, (variant = name, threads = n, prec = prec, seconds = s))
    end
  end
  n = maximum(threads)
  _set_flint_threads(n)
  s_plain = _time_thetas(tau_flint, squared_precision)
  s_sqr = _time_thetas(tau_flint, squared_precision; squared = true)
  println("squared = true at $squared_precision bits: $(round(s_sqr, digits = 2)) s ",
          "(plain: $(round(s_plain, digits = 2)) s)")
  push!(results, (variant = :flint_squared, threads = n, prec = squared_precision, seconds = s_sqr))
  t = change_base_ring(AcbField(jets_precision), tau_flint)
  CC = base_ring(t)
  s_jets = @elapsed Hecke.theta_jets([zero(CC) for _ in 1:g], t, 1)
  println("theta_jets of order 1 at $jets_precision bits: $(round(s_jets, digits = 2)) s")
  push!(results, (variant = :flint_jets1, threads = n, prec = jets_precision, seconds = s_jets))
  _set_flint_threads(old_threads)
  return results
end

################################################################################
#  Where inside FLINT: a profile, and the cost of a single theta constant
################################################################################

@doc raw"""
    theta_profile(tau; prec = 128, mincount = 20)

Profiles one Hecke.thetas call (acb_theta_all) at `prec` bits and prints
the flat profile including the C frames, sorted by count: the FLINT
functions (acb_theta_ql_*, acb_theta_sum_*, acb_theta_dist_*, ...) with the
most samples are where the time goes.
"""
function theta_profile(tau::AcbMatrix; prec::Int = 128, mincount::Int = 20)
  t = change_base_ring(AcbField(prec), tau)
  CC = base_ring(t)
  z = [zero(CC) for _ in 1:nrows(t)]
  Hecke.thetas(z, change_base_ring(AcbField(64), tau))          # compilation
  Profile.clear()
  Profile.init(n = 10^7, delay = 0.01)
  Profile.@profile Hecke.thetas(z, t)
  Profile.print(; C = true, format = :flat, sortedby = :count, mincount = mincount)
end

@doc raw"""
    time_single_theta(tau; prec = 128, characteristics = 3) -> Vector{Float64}

Times acb_theta_one (Hecke.theta) for a few characteristics at `prec` bits
(theta[0, 0] and random others). If one costs much less than
acb_theta_all / 2^(2g), the constants could be computed in parallel by
characteristic.
"""
function time_single_theta(tau::AcbMatrix; prec::Int = 128, characteristics::Int = 3)
  g = nrows(tau)
  t = change_base_ring(AcbField(prec), tau)
  CC = base_ring(t)
  z = [zero(CC) for _ in 1:g]
  Hecke.theta(z, change_base_ring(AcbField(64), tau), zeros(Int, 2*g))  # compilation
  times = Float64[]
  for k in 1:characteristics
    ab = k == 1 ? zeros(Int, 2*g) : rand(0:1, 2*g)
    s = @elapsed Hecke.theta(z, t, ab)
    println("theta$(ab) at $prec bits: $(round(s, digits = 2)) s")
    push!(times, s)
  end
  return times
end

@doc raw"""
    time_exact_versus_balls(tau; prec = 128) -> NamedTuple

Times Hecke.thetas for tau as given (balls; acb_theta propagates the radii
with low-precision derivatives, which Elkies-Kieffer report as expensive for
large g) and for its midpoint (exact entries), and compares the outputs:
the largest radius of each, and the largest distance between the midpoints
of the two results relative to the largest theta constant.
"""
function time_exact_versus_balls(tau::AcbMatrix; prec::Int = 128)
  t = change_base_ring(AcbField(prec), tau)
  t_exact = map_entries(Hecke.RiemannSurfaces._acb_mid, t)
  CC = base_ring(t)
  z = [zero(CC) for _ in 1:nrows(t)]
  Hecke.thetas(z, change_base_ring(AcbField(64), t_exact))       # compilation
  s_balls = @elapsed th_balls = Hecke.thetas(z, t)
  s_exact = @elapsed th_exact = Hecke.thetas(z, t_exact)
  radius(x) = Float64(Hecke.radius(real(x))) + Float64(Hecke.radius(imag(x)))
  mid(x) = Complex(_mid64(real(x)), _mid64(imag(x)))
  scale = maximum(abs(mid(x)) for x in values(th_balls))
  difference = maximum(abs(mid(th_balls[k]) - mid(th_exact[k])) for k in keys(th_balls))
  result = (seconds_balls = s_balls, seconds_exact = s_exact,
            max_radius_balls = maximum(radius, values(th_balls)) / scale,
            max_radius_exact = maximum(radius, values(th_exact)) / scale,
            max_radius_tau = maximum(radius(t[i, j]) for i in 1:nrows(t), j in 1:ncols(t)),
            relative_difference = difference / scale)
  println(result)
  return result
end

@doc raw"""
    compare_theta_duplication(tau; prec = 128, flint = true) -> NamedTuple

Times theta_constants_duplication (and, with `flint`, Hecke.thetas) at
`prec` bits on tau reduced by FLINT, and compares: the largest difference
relative to the largest constant, the sign margins.
"""
function compare_theta_duplication(tau::AcbMatrix; prec::Int = 128, flint::Bool = true)
  _, t = Hecke.siegel_reduction(change_base_ring(AcbField(prec), tau))
  RSM = Hecke.RiemannSurfaces
  RSM.theta_constants_duplication(change_base_ring(AcbField(64), t))        # compilation
  s_dup = @elapsed th, info = RSM.theta_constants_duplication(t)
  println("duplication: $(round(s_dup, digits = 2)) s, ", info)
  flint || return (seconds_duplication = s_dup, info = info)
  CC = base_ring(t)
  s_flint = @elapsed reference = Hecke.thetas([zero(CC) for _ in 1:nrows(t)], t)
  mid(x) = Complex(_mid64(real(x)), _mid64(imag(x)))
  scale = maximum(abs(mid(x)) for x in values(reference))
  difference = maximum(abs(mid(th[k]) - mid(reference[k])) for k in keys(reference)) / scale
  println("FLINT: $(round(s_flint, digits = 2)) s, relative difference $difference")
  return (seconds_duplication = s_dup, seconds_flint = s_flint, relative_difference = difference, info = info)
end

@doc raw"""
    time_needed_single_thetas(tau, characteristics; prec = 128) -> NamedTuple

Times theta_constants_single for the given characteristics (e.g.
used_theta_characteristics(5) from ReconstructGenusG.jl) on all threads.
"""
function time_needed_single_thetas(tau::AcbMatrix, characteristics; prec::Int = 128)
  _, t = Hecke.siegel_reduction(change_base_ring(AcbField(prec), tau))
  s = @elapsed Hecke.RiemannSurfaces.theta_constants_single(t, characteristics)
  println("$(length(characteristics)) constants on $(Threads.nthreads()) threads: $(round(s, digits = 2)) s")
  return (count = length(characteristics), seconds = s)
end

@doc raw"""
    debug_theta_duplication(tau; prec = 128)

Runs the levels of theta_constants_duplication and compares the values
theta[alpha; 0](0, 2^k tau) of each level with Hecke.thetas at 2^k tau
(FLINT; cheap for large k): prints per level the worst sign margin, the
worst relative difference to FLINT, and the worst alpha.
"""
function debug_theta_duplication(tau::AcbMatrix; prec::Int = 128)
  RSM = Hecke.RiemannSurfaces
  _, t0 = Hecke.siegel_reduction(change_base_ring(AcbField(prec), tau))
  g = nrows(t0)
  CC = AcbField(prec + 4*g + 20)
  t = change_base_ring(CC, t0)
  t = (t + transpose(t)) * inv(CC(2))
  X = [_mid64(real(t[i, j])) for i in 1:g, j in 1:g]
  Y = [_mid64(imag(t[i, j])) for i in 1:g, j in 1:g]
  Y = (Y + transpose(Y)) / 2
  lambda = RSM._smallest_eigenvalue64(Y)
  println("lambda (estimate) = $lambda, smallest eigenvalue = ", minimum(LinearAlgebra.eigvals(LinearAlgebra.Symmetric(Y))))
  bits = prec + 4*g + 20 + 10
  h = max(1, ceil(Int, log2(bits * log(2) / (pi * lambda)))) + 1
  scaled(k) = (2.0^k * X, 2.0^k * Y, sqrt(2.0^k) * RSM._cholesky_upper64(Y))
  key(alpha) = Tuple(vcat(RSM._characteristic_bits(alpha, g), zeros(Int, g)))
  function compare(T, k)
    tk = t * CC(2)^k
    reference = Hecke.thetas([zero(CC) for _ in 1:g], tk)
    worst, worst_alpha = 0.0, -1
    for alpha in 0:2^g-1
      r = reference[key(alpha)]
      d = abs(RSM._c64((T[alpha + 1] - r) / r))
      d > worst && ((worst, worst_alpha) = (d, alpha))
    end
    return worst, worst_alpha
  end
  Xk, Yk, Rk = scaled(h)
  T = RSM._theta_top_level(t * CC(2)^h, Xk, Yk, Rk, bits * log(2) / pi)
  println("level $h (top): relative difference to FLINT ", compare(T, h))
  for k in h-1:-1:1
    Xk, Yk, Rk = scaled(k)
    S = [sum(T[alpha + 1] * T[xor(alpha, beta) + 1] for alpha in 0:2^g-1) for beta in 0:2^g-1]
    worst_margin, worst_beta = 0.0, -1
    for beta in 0:2^g-1
      bins, qmin = RSM._theta_approximations64(Xk, Yk, Rk, RSM._characteristic_bits(beta, g))
      T[beta + 1], margin, _ = RSM._signed_root(S[beta + 1], bins[1], qmin)
      margin > worst_margin && ((worst_margin, worst_beta) = (margin, beta))
    end
    println("level $k: worst margin $worst_margin (beta $worst_beta), relative difference to FLINT ", compare(T, k))
  end
end
