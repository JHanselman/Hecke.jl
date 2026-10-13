################################################################################
#
#  Sampling points of Schottky-type loci in A_g (development code, Main)
#
#  A system of equations is evaluated on the theta constants of tau (signs
#  from acb_theta_all, so no sign data is needed). Points are found by
#  projecting random Siegel matrices onto the zero locus with Levenberg-Marquardt
#  (damped least squares, Jacobian by central differences at low
#  precision), classified with classify_jacobian and appended to a file.
#
#  Needs ReconstructGenusG.jl (classify_jacobian, prym_thetas_sq,
#  _loaded_sign_data) and ReconstructGenusGTests.jl (random_siegel_matrix).
#
################################################################################

using Random

################################################################################
#
#  Equation systems
#
################################################################################

@doc raw"""
    ThetaEquationSystem

A system of equations in the theta constants: `residual(g, thetas, state)`
returns (values, state) for the theta constants `thetas` (a dictionary
characteristic => value) of a matrix in Siegel space; `state` is nothing on
the first call at a point and is passed back unchanged while the Jacobian is
computed (e.g. the choice of normalization). The values should be invariant
under scaling all theta constants by one factor (normalized). Each matrix T
in `transforms` (symplectic 2g x 2g) contributes the residual at T(tau), e.g.
the equations for the period T^-1(eta) instead of eta.
"""
struct ThetaEquationSystem
  name::String
  residual::Function
  transforms::Vector{ZZMatrix}
end

@doc raw"""
    theta_equation_system(name, f, degree; transforms = nothing) -> ThetaEquationSystem

A system from a function f(g, thetas) -> Vector of homogeneous polynomials of
degree `degree` in the theta constants (e.g. a port of `accola` or `fgsm`
from Theta.jl), normalized by the largest even theta constant to the power
`degree`.
"""
function theta_equation_system(name::String, f::Function, degree::Int; transforms = nothing)
  function residual(g, thetas, state)
    key = state === nothing ? argmax(k -> RSR._abs64(thetas[k]), collect(keys(thetas))) : state
    c = inv(thetas[key])^degree
    return [v * c for v in f(g, thetas)], key
  end
  return ThetaEquationSystem(name, residual, transforms === nothing ? ZZMatrix[] : collect(transforms))
end

# The residual of the system at tau (all transforms), with the states.
function _system_residual(S::ThetaEquationSystem, tau::AcbMatrix, states = nothing)
  g = nrows(tau)
  CC = base_ring(tau)
  transforms = isempty(S.transforms) ? [identity_matrix(ZZ, 2*g)] : S.transforms
  values = AcbFieldElem[]
  new_states = Any[]
  for (i, T) in enumerate(transforms)
    t = isone(T) ? tau : Hecke.siegel_transform(T, tau)
    thetas = Hecke.thetas([zero(CC) for _ in 1:g], t)
    v, state = S.residual(g, thetas, states === nothing ? nothing : states[i])
    append!(values, v)
    push!(new_states, state)
  end
  return values, new_states
end

@doc raw"""
    random_eta_transforms(g, count; seed = 1) -> Vector{ZZMatrix}

`count` symplectic matrices T (the identity first) with distinct
T^-1 (0..0; 1 0..0) mod 2, products of random elementary symplectic
matrices [1 S; 0 1], [1 0; S 1] with S symmetric 0/1.
"""
function random_eta_transforms(g::Int, count::Int; seed::Int = 1)
  rng = Random.MersenneTwister(seed)
  I = identity_matrix(ZZ, g)
  Z = zero_matrix(ZZ, g, g)
  function elementary()
    S = zero_matrix(ZZ, g, g)
    for i in 1:g, j in i:g
      S[i, j] = S[j, i] = rand(rng, 0:1)
    end
    return rand(rng, Bool) ? [I S; Z I] : [I Z; S I]
  end
  eta = zero_matrix(ZZ, 2*g, 1)
  eta[g + 1, 1] = 1
  key(T) = (v = inv(T) * eta; [Int(mod(v[i, 1], 2)) for i in 1:2*g])
  result = [identity_matrix(ZZ, 2*g)]
  seen = Set([key(result[1])])
  tries = 0
  while length(result) < count && tries < 1000 * count
    tries += 1
    T = prod(elementary() for _ in 1:4)
    k = key(T)
    k in seen && continue
    push!(seen, k)
    push!(result, T)
  end
  return result
end

################################################################################
#
#  Projection onto the zero locus
#
################################################################################

# tau at the precision of CC as an exact point (the midpoints: the sampled
# points are points, their radii from earlier steps are irrelevant).
_change_precision(tau::AcbMatrix, CC::AcbField) =
  matrix(CC, nrows(tau), ncols(tau), [CC(Hecke.midpoint(real(tau[i, j])), Hecke.midpoint(imag(tau[i, j])))
                                      for i in 1:nrows(tau) for j in 1:ncols(tau)])

_upper_coordinates(g::Int) = [(i, j) for i in 1:g for j in i:g]

function _add_symmetric!(tau::AcbMatrix, i::Int, j::Int, x::AcbFieldElem)
  tau[i, j] += x
  i != j && (tau[j, i] += x)
  return tau
end

_max_log2(values) = maximum(v -> RSR._safe_log2(RSR._abs64(v)), values; init = -Inf)

# Whether the imaginary part of tau is positive definite (Float64).
function _in_siegel_space(tau::AcbMatrix)
  g = nrows(tau)
  Y = [Float64(imag(RSR._c64(tau[i, j]))) for i in 1:g, j in 1:g]
  return minimum(RSR.LinearAlgebra.eigvals(RSR.LinearAlgebra.Symmetric(Y))) > 0
end

@doc raw"""
    residual_jacobian(S, tau, states; prec = 128, step = 2.0^-30, method = :heat) -> Matrix{ComplexF64}

The Jacobian of the residual of S with respect to the upper triangle of tau
(the normalization `states` fixed), at precision `prec`. With
`method = :heat` (only for S without transforms) from one call of
theta_jets of order 2: by the heat equation the derivative of every theta
constant with respect to the coordinate tau_jk = tau_kj is c_jk / (2 pi i),
c_jk the coefficient of z_j z_k in its Taylor expansion, and the residual is
differentiated by central differences in the theta constants (no further
theta evaluations). With `method = :difference` by central differences in
tau (2 theta evaluations per coordinate).
"""
function residual_jacobian(S::ThetaEquationSystem, tau::AcbMatrix, states; prec::Int = 128,
                           step::Float64 = 2.0^-30, method::Symbol = :heat)
  @req method in (:heat, :difference) "method must be :heat or :difference."
  g = nrows(tau)
  CC = AcbField(prec)
  t = _change_precision(tau, CC)
  h = CC(step)
  columns = Vector{Vector{ComplexF64}}()
  if method === :heat && all(isone, S.transforms)
    jets = Hecke.theta_jets([zero(CC) for _ in 1:g], t, 2)
    origin = ntuple(_ -> 0, g)
    characteristics = collect(keys(jets))
    thetas = Dict(c => jets[c][origin] for c in characteristics)
    factor = inv(2 * const_pi(CC) * onei(CC))
    state = states === nothing ? nothing : states[1]
    for (i, j) in _upper_coordinates(g)
      exponent = ntuple(l -> (l == i) + (l == j), g)
      derivatives = Dict(c => factor * jets[c][exponent] for c in characteristics)
      plus, _ = S.residual(g, Dict(c => thetas[c] + h * derivatives[c] for c in characteristics), state)
      minus, _ = S.residual(g, Dict(c => thetas[c] - h * derivatives[c] for c in characteristics), state)
      push!(columns, [RSR._c64((p - m) / (2 * h)) for (p, m) in zip(plus, minus)])
    end
    J = reduce(hcat, columns)
    @req all(isfinite, J) "The Jacobian is not finite (a square root at a vanishing product of theta constants: use the product form of the equations, e.g. accola_system(product = true))."
    return J
  end
  for (i, j) in _upper_coordinates(g)
    plus, _ = _system_residual(S, _add_symmetric!(deepcopy(t), i, j, h), states)
    minus, _ = _system_residual(S, _add_symmetric!(deepcopy(t), i, j, -h), states)
    push!(columns, [RSR._c64((p - m) / (2 * h)) for (p, m) in zip(plus, minus)])
  end
  return reduce(hcat, columns)
end

# The numerical rank: the largest gap of the singular values above
# s_1 * 2^-min_log2 (all of them without a gap of more than gap_bits bits).
function _numerical_rank(s::Vector{Float64}; gap_bits::Float64 = 10.0, min_log2::Float64 = 40.0)
  l = [RSR._safe_log2(x) for x in s]
  r, best = length(l), 0.0
  for i in 1:length(l)-1
    l[i + 1] < l[1] - min_log2 && return best >= gap_bits ? r : i
    gap = l[i] - l[i + 1]
    gap > best && ((r, best) = (i, gap))
  end
  return best >= gap_bits ? r : length(l)
end

# log2 of the Euclidean norm of the midpoints of a vector of balls.
function _log2_norm(values)
  m = _max_log2(values)
  m == -Inf && return -Inf
  return m + 0.5 * log2(sum(abs2(RSR._abs64(v) * 2.0^(-m)) for v in values))
end

@doc raw"""
    project_to_locus(S, tau; prec = 1024, max_iterations = 80, max_trials = 12, max_step = 0.25,
                     jacobian_prec = 128, jacobian_every = 8, codimension = nothing,
                     extrapolate = true, jacobian = nothing, final_jacobian = true,
                     verbose = false) -> NamedTuple

Levenberg-Marquardt for the residual of S from tau: the step
-V diag(s/(s^2 + lambda)) U^* F from the singular value decomposition of the
Jacobian (only the first `codimension` singular values if given), accepted
if it decreases |F| (with the normalization of F fixed), otherwise lambda is
raised (by 2^4, at most `max_trials` times); after an accepted step lambda
is lowered, down to s_1^2 2^-80 (the accuracy of the Jacobian). The damping
also takes care of excess intersections (more equations than the
codimension, as for Accola and FGSM): the singular values that tend to 0
near the locus are damped out.

The Jacobian (residual_jacobian, the expensive part) is computed afresh
only every `jacobian_every` iterations, when the normalization of the
residual changed (e.g. another sign pattern) or when no step was accepted;
in between it is updated by Broyden's rank one formula from the accepted
steps. Steps are limited to max_step per entry; the working precision is
doubled from 128 bits up to `prec` whenever the residual is near it.

With `extrapolate`, when successive accepted steps are (nearly) parallel and
shrink by a stable factor c (linear convergence, as at a zero of higher
multiplicity), the step d/(1 - c) (Aitken) is tried as well and taken if
its residual is smaller.

A Jacobian near tau (e.g. the `jacobian` of a previous projection nearby)
can be passed as `jacobian` to start with instead of a fresh one; without
`final_jacobian` the rank and tangent space at a converged point come from
the updated Jacobian instead of a fresh one.

Returns (tau, status (:converged, :stalled, :max_iterations), residual_log2,
iterations, jacobians (the number computed), extrapolated, rank (at a
converged point the numerical rank of a fresh Jacobian there, the local
codimension), tangent (at a converged point an orthonormal basis of the
kernel of that Jacobian, coordinates the upper triangle of tau), jacobian
(the last Jacobian),
singular_values_log2 (at the last point), history).
"""
function project_to_locus(S::ThetaEquationSystem, tau::AcbMatrix; prec::Int = 1024,
                          max_iterations::Int = 80, max_trials::Int = 12, max_step::Float64 = 0.25,
                          jacobian_prec::Int = 128, jacobian_every::Int = 8, codimension = nothing,
                          extrapolate::Bool = true, jacobian = nothing, final_jacobian::Bool = true,
                          verbose::Bool = false)
  g = nrows(tau)
  coordinates = _upper_coordinates(g)
  working = min(128, prec)
  t = _change_precision(tau, AcbField(working))
  history = Float64[]
  status = :max_iterations
  rank, singular_values = 0, Float64[]
  damping_bits = -10.0
  # the previous accepted step: the direction (unit vector) and log2 of its length
  previous_direction, previous_log2 = ComplexF64[], -Inf
  extrapolated = 0
  # the Jacobian, its age (Broyden updates since it was computed), the number
  # computed, and the residual at t with the previous normalization
  J, age, jacobians, predicted = nothing, 0, 0, nothing
  # a given Jacobian (or the one from before a change of precision) is used
  # without the check of the normalization
  trusted = false
  if jacobian !== nothing
    J, age, trusted = copy(jacobian), 1, true
  end
  tangent = zeros(ComplexF64, length(coordinates), 0)
  time_residual, time_jacobian = 0.0, 0.0
  for iteration in 1:max_iterations
    CC = AcbField(working)
    clock = time()
    values, states = _system_residual(S, t, nothing)
    time_residual = time() - clock
    r = _max_log2(values)
    push!(history, r)
    verbose && println("iteration $iteration: precision $working, residual 2^$(round(r, digits = 1))",
                       isempty(singular_values) ? "" :
                       ", damping 2^$(damping_bits), Jacobian age $age, singular values 2^" *
                       string(round.(RSR._safe_log2.(singular_values), digits = 1)) *
                       " (residual $(round(time_residual, digits = 2)) s, last Jacobian $(round(time_jacobian, digits = 2)) s)")
    if r < -(working - 40)
      if working == prec
        status = :converged
        # the local codimension at the point (full decomposition: the kernel)
        if final_jacobian || J === nothing
          clock = time()
          J = residual_jacobian(S, t, states; prec = jacobian_prec)
          time_jacobian = time() - clock
          jacobians += 1
        end
        decomposition = RSR.LinearAlgebra.svd(J; full = true)
        singular_values = decomposition.S
        rank = _numerical_rank(singular_values)
        tangent = decomposition.V[:, rank+1:end]
        break
      end
      working = min(2 * working, prec)
      t = _change_precision(t, AcbField(working))
      predicted, trusted = nothing, J !== nothing
      continue
    end
    # the normalization changed if the residual differs from the one with the
    # previous normalization at this point
    changed = predicted === nothing ? !trusted :
              _max_log2([v - p for (v, p) in zip(values, predicted)]) > r - 10
    trusted = false
    if J === nothing || age >= jacobian_every || changed
      clock = time()
      J = residual_jacobian(S, t, states; prec = jacobian_prec)
      time_jacobian = time() - clock
      jacobians += 1
      age = 0
    end
    decomposition = RSR.LinearAlgebra.svd(J)
    singular_values = decomposition.S
    n = codimension === nothing ? length(singular_values) : min(codimension, length(singular_values))
    rank = n
    s, V = singular_values[1:n], decomposition.V[:, 1:n]
    e = round(Int, r)
    scaled = [RSR._c64(v * CC(2)^(-e)) for v in values]
    components = decomposition.U[:, 1:n]' * scaled
    current = _log2_norm(values)
    accepted = false
    for trial in 1:max_trials
      lambda = s[1]^2 * 2.0^damping_bits
      d = -(V * (components .* s ./ (s .^ 2 .+ lambda)))
      largest = maximum(abs, d) * 2.0^e
      factor = largest > max_step ? max_step / largest : 1.0
      step = d * factor
      candidate = deepcopy(t)
      for (k, (i, j)) in enumerate(coordinates)
        _add_symmetric!(candidate, i, j, CC(real(step[k]), imag(step[k])) * CC(2)^e)
      end
      _in_siegel_space(candidate) || (damping_bits += 4; continue)
      new_values = first(_system_residual(S, candidate, states))
      new_norm = _log2_norm(new_values)
      if new_norm < current
        step_log2 = log2(sum(abs2, step)) / 2 + e
        direction = step / sqrt(sum(abs2, step))
        if extrapolate && !isempty(previous_direction)
          c = 2.0^(step_log2 - previous_log2)
          cosine = abs(sum(conj.(previous_direction) .* direction))
          if cosine > 0.99 && 0.2 < c < 0.95
            further = deepcopy(candidate)
            for (k, (i, j)) in enumerate(coordinates)
              x = step[k] * c / (1 - c)
              _add_symmetric!(further, i, j, CC(real(x), imag(x)) * CC(2)^e)
            end
            if _in_siegel_space(further)
              further_values = first(_system_residual(S, further, states))
              if _log2_norm(further_values) < new_norm
                candidate, new_values = further, further_values
                step = step / (1 - c)
                extrapolated += 1
              end
            end
          end
        end
        # Broyden: J += (dF - J dx) dx^* / |dx|^2 (both scaled by 2^-e)
        dF = [RSR._c64((nv - v) * CC(2)^(-e)) for (nv, v) in zip(new_values, values)]
        J = J + (dF - J * step) * step' / sum(abs2, step)
        age += 1
        previous_direction, previous_log2 = direction, step_log2
        t = candidate
        predicted = new_values
        accepted = true
        damping_bits = max(damping_bits - 4, -80.0)
        break
      end
      damping_bits += 4
    end
    if !accepted
      if age > 0
        # an updated Jacobian may be too inaccurate: retry with a fresh one
        J, predicted = nothing, nothing
        damping_bits = -10.0
        continue
      end
      status = :stalled
      break
    end
  end
  return (tau = t, status = status, residual_log2 = isempty(history) ? Inf : history[end],
          iterations = length(history), jacobians = jacobians, extrapolated = extrapolated, rank = rank,
          tangent = tangent, jacobian = J, singular_values_log2 = [RSR._safe_log2(x) for x in singular_values], history = history)
end

################################################################################
#
#  Sampling and storage
#
################################################################################

_tau_string(tau::AcbMatrix) = setprecision(BigFloat, precision(base_ring(tau)) + 16) do
  join([string(BigFloat(real(tau[i, j]))) * "," * string(BigFloat(imag(tau[i, j])))
        for (i, j) in _upper_coordinates(nrows(tau))], ";")
end

function _tau_from_string(s::AbstractString, g::Int, prec::Int)
  CC = AcbField(prec)
  RR = ArbField(prec)
  tau = zero_matrix(CC, g, g)
  setprecision(BigFloat, prec + 16) do
    for ((i, j), entry) in zip(_upper_coordinates(g), split(s, ";"))
      re, im = split(entry, ",")
      tau[i, j] = tau[j, i] = CC(RR(parse(BigFloat, re)), RR(parse(BigFloat, im)))
    end
  end
  return tau
end

_field_string(x) = replace(string(x), r"[\t\n]" => " ")

# Classifies a projected point (if converged) and returns the record of a
# sample. The point lies on the locus only up to about 2^-(prec - 40) (the
# convergence criterion of project_to_locus), while classify_jacobian treats
# its input as exact: so it is classified at the lower precision
# classify_prec (default prec - 80), where that distance is below the
# rounding errors (otherwise e.g. the Schottky-Jung relations fail at
# precision prec).
function _sample_record(S::ThetaEquationSystem, p, n::Int, sample_seed::Int, origin::Symbol, t0::Float64;
                        g::Int, prec::Int, classify::Bool, reduce::Bool, pairs_prym, fay_relations,
                        prym_fay_relations, classify_prec = nothing)
  t_project = time() - t0
  verdict, stage, evidence, t_classify = :none, :none, nothing, 0.0
  if classify && p.status === :converged
    t1 = time()
    tau_classify = _change_precision(p.tau, AcbField(classify_prec === nothing ? prec - 80 : classify_prec))
    tau_reduced = reduce ? Hecke.siegel_reduction(tau_classify)[2] : tau_classify
    CC = base_ring(tau_reduced)
    thetas = Hecke.thetas([zero(CC) for _ in 1:g], tau_reduced)
    c = classify_jacobian(g, thetas; sign_data = pairs_prym, fay_relations = fay_relations,
                          prym_fay_relations = prym_fay_relations)
    verdict, stage, evidence, t_classify = c.verdict, c.stage, c.evidence, time() - t1
  end
  return (index = n, seed = sample_seed, system = S.name, origin = origin, status = p.status,
          verdict = verdict, stage = stage, prec = prec, residual_log2 = round(p.residual_log2, digits = 1),
          iterations = p.iterations, jacobians = p.jacobians, rank = p.rank,
          singular_values_log2 = round.(p.singular_values_log2, digits = 1),
          time_projection = round(t_project, digits = 1), time_classification = round(t_classify, digits = 1),
          evidence = evidence, tau = p.tau)
end

_error_record(S, n, sample_seed, origin, prec, err) =
  (index = n, seed = sample_seed, system = S.name, origin = origin, status = :error, verdict = :none,
   stage = :none, prec = prec, error = sprint(showerror, err))

function _write_record(file::AbstractString, record)
  fields = [string(k) * "=" * (k === :tau ? _tau_string(record[k]) : _field_string(record[k])) for k in keys(record)]
  open(file, "a") do io
    println(io, join(["sample"; fields], "\t"))
  end
end

_sample_count(file) = isfile(file) ? Base.count(l -> startswith(l, "sample"), eachline(file)) : 0

function _report_record!(tallies, record, t0; verbose::Bool)
  key = record.status === :converged ? record.verdict : record.status
  tallies[key] = get(tallies, key, 0) + 1
  verbose && println("sample $(record.index): $(record.status) $(record.verdict) ($(record.stage)), ",
                     hasproperty(record, :residual_log2) ? "residual 2^$(record.residual_log2), rank $(record.rank), " : "",
                     round(time() - t0, digits = 1), " s")
end

@doc raw"""
    sample_schottky_locus(S, count; file, g = 5, prec = 1024, seed = 1, starts = nothing,
                          classify = true, reduce = true, sign_data = nothing, fay_relations = nothing,
                          prym_fay_relations = nothing, scale = 1.0, max_iterations = 80,
                          codimension = nothing, verbose = true) -> Vector{NamedTuple}

Projects `count` starting matrices onto the zero locus of S (project_to_locus),
classifies the converged points with classify_jacobian (at the Siegel
reduction of tau if `reduce`, at precision classify_prec, default prec - 80,
as the points are on the locus up to about 2^-(prec - 40) only; theta
constants from acb_theta_all) and
appends one line per sample to `file` (tab separated key=value; tau as the
upper triangle with all digits; see load_schottky_samples). The starting
matrices are random_siegel_matrix(g, 128; scale), or starts(n) for a function
`starts` (e.g. perturbations of known points of the locus, see
perturbed_siegel_matrix), seeded by seed and the sample index n. Appending
to an existing file continues its numbering, so runs with different seeds
(or in parallel processes with different files) can be combined. Errors are
recorded (status = :error) rather than raised.
"""
function sample_schottky_locus(S::ThetaEquationSystem, count::Int; file::AbstractString, g::Int = 5,
                               prec::Int = 1024, seed::Int = 1, starts = nothing, classify::Bool = true,
                               reduce::Bool = true, sign_data = nothing, fay_relations = nothing,
                               prym_fay_relations = nothing, scale::Float64 = 1.0,
                               max_iterations::Int = 80, codimension = nothing, classify_prec = nothing,
                               verbose::Bool = true)
  pairs_prym = classify ? _loaded_sign_data(sign_data, g - 1) : nothing
  start = _sample_count(file)
  results = NamedTuple[]
  tallies = Dict{Symbol, Int}()
  origin = starts === nothing ? :random : :start
  for n in start+1:start+count
    sample_seed = 1_000_000 * seed + n
    Random.seed!(sample_seed)
    t0 = time()
    record = try
      tau0 = starts === nothing ? random_siegel_matrix(g, 128; scale = scale) : starts(n)
      p = project_to_locus(S, tau0; prec = prec, max_iterations = max_iterations, codimension = codimension)
      _sample_record(S, p, n, sample_seed, origin, t0; g = g, prec = prec, classify = classify, reduce = reduce,
                     pairs_prym = pairs_prym, fay_relations = fay_relations, prym_fay_relations = prym_fay_relations,
                     classify_prec = classify_prec)
    catch err
      err isa InterruptException && rethrow()
      _error_record(S, n, sample_seed, origin, prec, err)
    end
    _write_record(file, record)
    push!(results, record)
    _report_record!(tallies, record, t0; verbose = verbose)
  end
  verbose && println("summary: ", join(["$k: $v" for (k, v) in tallies], ", "))
  return results
end

@doc raw"""
    perturbed_siegel_matrix(tau, size) -> AcbMatrix

tau plus a random complex symmetric matrix with entries of absolute value at
most `size` (retried until the imaginary part is positive definite).
"""
function perturbed_siegel_matrix(tau::AcbMatrix, size::Float64)
  CC = base_ring(tau)
  g = nrows(tau)
  while true
    t = _change_precision(tau, CC)
    for (i, j) in _upper_coordinates(g)
      _add_symmetric!(t, i, j, CC(size * (2 * rand() - 1), size * (2 * rand() - 1)))
    end
    _in_siegel_space(t) && return t
  end
end

@doc raw"""
    walk_schottky_locus(S, tau, count; file, step_size = 0.05, prec = 1024, seed = 1,
                        classify = true, reduce = true, sign_data = nothing, fay_relations = nothing,
                        prym_fay_relations = nothing, max_iterations = 40, jacobian_refresh = 3,
                        verbose = true, verbose_projection = false) -> Vector{NamedTuple}

A random walk on the component of the zero locus of S through (a point near)
tau: from the current point a step of length `step_size` in a random
direction of the tangent space (the kernel of the Jacobian at the point,
project_to_locus), then projected back onto the locus. Each new point is
classified and recorded as in sample_schottky_locus (origin = :walk). When a
projection fails the step size is halved (at most 4 times) and the walk
continues from the last point. Each projection starts with the Jacobian of
the previous point (Broyden updates), and a fresh Jacobian is computed at
every `jacobian_refresh`-th point only (the expensive part, minutes at a
Jacobian of genus 5). The walk stays on one component (unless it
passes a singular point), so with a Jacobian as tau it samples J_g, from a
point of another component that component.
"""
function walk_schottky_locus(S::ThetaEquationSystem, tau::AcbMatrix, count::Int; file::AbstractString,
                             step_size::Float64 = 0.05, prec::Int = 1024, seed::Int = 1,
                             classify::Bool = true, reduce::Bool = true, sign_data = nothing,
                             fay_relations = nothing, prym_fay_relations = nothing,
                             max_iterations::Int = 40, jacobian_refresh::Int = 3, classify_prec = nothing,
                             verbose::Bool = true, verbose_projection::Bool = false)
  g = nrows(tau)
  pairs_prym = classify ? _loaded_sign_data(sign_data, g - 1) : nothing
  current = project_to_locus(S, tau; prec = prec, max_iterations = max_iterations, verbose = verbose_projection)
  @req current.status === :converged "The starting point does not project onto the locus ($(current.status))."
  verbose && println("start: rank $(current.rank), tangent space of dimension $(size(current.tangent, 2))")
  start = _sample_count(file)
  coordinates = _upper_coordinates(g)
  results = NamedTuple[]
  tallies = Dict{Symbol, Int}()
  for n in start+1:start+count
    sample_seed = 1_000_000 * seed + n
    Random.seed!(sample_seed)
    t0 = time()
    record = nothing
    h = step_size
    for attempt in 1:5
      record = try
        T = current.tangent
        direction = T * (randn(ComplexF64, size(T, 2)))
        direction /= maximum(abs, direction)
        CC = base_ring(current.tau)
        t = _change_precision(current.tau, AcbField(128))
        for (k, (i, j)) in enumerate(coordinates)
          _add_symmetric!(t, i, j, AcbField(128)(real(h * direction[k]), imag(h * direction[k])))
        end
        p = project_to_locus(S, t; prec = prec, max_iterations = max_iterations, jacobian = current.jacobian,
                             final_jacobian = n % jacobian_refresh == 0, verbose = verbose_projection)
        verbose && println("  step of size $h: $(p.status), residual 2^$(round(p.residual_log2, digits = 1)), ",
                           "$(p.iterations) iterations, $(p.jacobians) Jacobians, ", round(time() - t0, digits = 1), " s")
        p.status === :converged && (current = p)
        _sample_record(S, p, n, sample_seed, :walk, t0; g = g, prec = prec, classify = classify, reduce = reduce,
                       pairs_prym = pairs_prym, fay_relations = fay_relations, prym_fay_relations = prym_fay_relations,
                     classify_prec = classify_prec)
      catch err
        err isa InterruptException && rethrow()
        _error_record(S, n, sample_seed, :walk, prec, err)
      end
      record.status === :converged && break
      h /= 2
    end
    _write_record(file, record)
    push!(results, record)
    _report_record!(tallies, record, t0; verbose = verbose)
  end
  verbose && println("summary: ", join(["$k: $v" for (k, v) in tallies], ", "))
  return results
end

@doc raw"""
    load_schottky_samples(file; g = 5) -> Vector{Dict{Symbol, Any}}

The samples of sample_schottky_locus: every field as a string except tau
(an AcbMatrix at the stored precision, exact midpoints), prec, index, seed,
iterations, rank (Int), residual_log2 (Float64), status, verdict and stage
(Symbol).
"""
function load_schottky_samples(file::AbstractString; g::Int = 5)
  samples = Dict{Symbol, Any}[]
  for line in eachline(file)
    startswith(line, "sample") || continue
    d = Dict{Symbol, Any}()
    for field in split(line, "\t")[2:end]
      k, v = split(field, "="; limit = 2)
      d[Symbol(k)] = v
    end
    for k in (:prec, :index, :seed, :iterations, :jacobians, :rank)
      haskey(d, k) && (d[k] = parse(Int, d[k]))
    end
    haskey(d, :residual_log2) && (d[:residual_log2] = parse(Float64, d[:residual_log2]))
    for k in (:status, :verdict, :stage, :origin)
      haskey(d, k) && (d[k] = Symbol(d[k]))
    end
    haskey(d, :tau) && (d[:tau] = _tau_from_string(d[:tau], g, d[:prec]))
    push!(samples, d)
  end
  return samples
end

################################################################################
#
#  Theta constants of Jacobians and of Pryms of plane quintics
#
#  For the interpolation only theta constants are needed: points of J_5 from
#  random canonical curves of genus 5, points of the locus of intermediate
#  Jacobians of cubic threefolds (and of Jacobians, depending on the type)
#  from the Pryms of random plane quintics for eta = (0..0; 1 0..0).
#
################################################################################

# The values of the theta constants at the even characteristics, to the
# precision they are known (relative radius), as strings.
function _theta_values_string(thetas, g::Int)
  chars = even_theta_characteristics(g)
  values = [thetas[Tuple(c)] for c in chars]
  bits = max(64, floor(Int, -RSR._log2_relative_radius(values)))
  return bits, setprecision(BigFloat, bits + 16) do
    join([string(BigFloat(Hecke.midpoint(real(v)))) * "," * string(BigFloat(Hecke.midpoint(imag(v))))
          for v in values], ";")
  end
end

@doc raw"""
    sample_theta_data(kind, count; file, prec = 500, seed = 1, coefficients = -3:3, classify = true,
                      curve_sign_data_5 = nothing, curve_sign_data_6 = nothing, sign_data_4 = nothing,
                      fay_relations_6 = nothing, verbose = true) -> Vector{NamedTuple}

Theta constants of genus 5 for `count` random curves, appended to `file` one
line per sample (tab separated key=value, see load_theta_data):
- kind = :jacobian: the Jacobian of a random canonical curve of genus 5
  (canonical_test_curve_g5);
- kind = :quintic: the Prym of a random smooth plane quintic
  (plane_quintic_test_curve) for eta = (0..0; 1 0..0), with kappa = O(1)
  (the odd characteristic of genus 6 with vanishing gradient) and the type
  :intermediate_jacobian (kappa + eta odd, i.e. kappa[1] = 0; Mumford) or
  :jacobian.
Each line has `valid` (the theta constants known to at least prec/2 bits,
their signs determined, and for Jacobians Accola's equations vanishing to
half the precision: they vanish on J_5, so this checks the theta constants
and their signs; on intermediate Jacobians some of the 8 relations need not
vanish, see accola_pattern: per relation 0 if it vanishes, 1 if not),
the curve, the type, the verdict and stage of classify_jacobian
(with `classify`), log2 of the largest residual of Accola's equations
(sign_pattern_relations, should be about -precision), the precision (bits) of
the theta constants and their values at even_theta_characteristics(5) (in
that order). Theta constants by theta_constants_riemann_signs with the
genus 5 or 6 sign data; signs of the Prym by Riemann's relations (genus 5
sign data). Errors are recorded (status = :error).

Resumable and without duplicates: the samples are numbered in the file
(appending continues the numbering) and sample n is drawn from the random
seed 10^6 seed + n, so an interrupted run continued later gives the same
samples as an uninterrupted one. Ctrl-C during a sample (e.g. a curve on
which the computation hangs) records that sample as an error "interrupted"
and ends the run, so a rerun continues with the next curve. A curve
that is already in `file` or in one of `other_files` (e.g. the files of
parallel runs, with other seeds) is replaced by the next one drawn.
"""
function sample_theta_data(kind::Symbol, count::Int; file::AbstractString, prec::Int = 500, seed::Int = 1,
                           coefficients = -3:3, classify::Bool = true, curve_sign_data_5 = nothing,
                           curve_sign_data_6 = nothing, sign_data_4 = nothing, fay_relations_6 = nothing,
                           other_files = String[], verbose::Bool = true)
  @req kind in (:jacobian, :quintic) "kind must be :jacobian or :quintic."
  data5 = _loaded_sign_data(curve_sign_data_5, 5)
  data6 = kind === :quintic ? _loaded_sign_data(curve_sign_data_6, 6) : nothing
  data4 = classify ? _loaded_sign_data(sign_data_4, 4) : nothing
  odds6 = odd_theta_characteristics(6)
  accola = accola_characteristics()
  start = _sample_count(file)
  seen = Set{String}()
  for f in [file; other_files]
    isfile(f) || continue
    for line in eachline(f)
      m = match(r"\tcurve=([^\t]*)", line)
      m === nothing || push!(seen, m.captures[1])
    end
  end
  function new_curve()
    for _ in 1:1000
      c = kind === :jacobian ? canonical_test_curve_g5(; coefficients = coefficients) :
                               plane_quintic_test_curve(; coefficients = coefficients)
      key = _field_string(kind === :jacobian ? c.plane : c)
      key in seen || (push!(seen, key); return c)
    end
    error("No new curve found in 1000 tries (enlarge the coefficients).")
  end
  tallies = Dict{Any, Int}()
  results = NamedTuple[]
  interrupted = false
  for n in start+1:start+count
    sample_seed = 1_000_000 * seed + n
    Random.seed!(sample_seed)
    t0 = time()
    record = try
      if kind === :jacobian
        curve = new_curve()
        F = curve.plane
        RS = riemann_surface_with_differentials(curve.plane, curve.numerators, prec)
        tau = Hecke.siegel_reduction(_small_period_matrix(RSR.big_period_matrix(RS)))[2]
        thetas = _theta_constants_by_method(tau, :riemann; curve_sign_data = data5, certified_fixed_signs = false)
        type, kappa, sufficient = :jacobian, nothing, true
      else
        F = new_curve()
        RS = RSR.riemann_surface(F, prec; superelliptic = false, model = :original)
        tau6 = Hecke.siegel_reduction(_small_period_matrix(RSR.big_period_matrix(RS)))[2]
        thetas6 = _theta_constants_by_method(tau6, :riemann; curve_sign_data = data6, certified_fixed_signs = false)
        K, _ = odd_theta_gradient_kernel(6, thetas6; relations = fay_relations_6)
        norms = [maximum(RSR._abs64(K[r, c]) for c in 1:6) for r in 1:nrows(K)]
        order = sortperm(norms)
        kappa = odds6[order[1]]
        type = isodd(kappa[1]) ? :jacobian : :intermediate_jacobian
        thetas, sufficient = _prym_theta_constants(6, thetas6, data5)
      end
      verdict, stage = :none, :none
      if classify
        c = classify_jacobian(5, thetas; sign_data = data4)
        verdict, stage = c.verdict, c.stage
      end
      accola_values = first(sign_pattern_relations(thetas, accola))
      accola_log2 = round(_max_log2(accola_values), digits = 1)
      # per relation whether it vanishes (to half the precision)
      accola_pattern = join([RSR._safe_log2(RSR._abs64(v)) < -div(prec, 4) ? "0" : "1" for v in accola_values])
      bits, values = _theta_values_string(thetas, 5)
      # Accola's equations vanish on J_5 (a check of the theta constants and
      # their signs), but not on every intermediate Jacobian: for those some
      # relations may not vanish (accola_pattern), depending on the
      # characteristics
      valid = bits >= div(prec, 2) && (type !== :jacobian || accola_log2 < -div(bits, 2)) && sufficient
      (index = n, seed = sample_seed, kind = kind, status = :ok, valid = valid, curve = string(F),
       kappa = kappa === nothing ? "" : join(kappa, ","), type = type, verdict = verdict, stage = stage,
       accola_log2 = accola_log2, accola_pattern = accola_pattern, signs_sufficient = sufficient, prec = prec, bits = bits,
       time = round(time() - t0, digits = 1), thetas = values)
    catch err
      # an interrupt (Ctrl-C, e.g. on a curve that hangs) records the sample as
      # skipped and ends the run: a rerun continues with the next curve
      err isa InterruptException && (interrupted = true)
      (index = n, seed = sample_seed, kind = kind, status = :error,
       error = err isa InterruptException ? "interrupted" : sprint(showerror, err))
    end
    open(file, "a") do io
      println(io, join(["sample"; [string(k) * "=" * (k === :thetas ? record[k] : _field_string(record[k]))
                                   for k in keys(record)]], "\t"))
    end
    push!(results, Base.structdiff(record, NamedTuple{(:thetas,)}))
    key = record.status === :ok ? (record.valid ? (record.type, record.verdict) : :invalid) : :error
    tallies[key] = get(tallies, key, 0) + 1
    verbose && println("sample $n: ", record.status === :ok ?
                       "$(record.type), $(record.verdict) ($(record.stage)), Accola 2^$(record.accola_log2), " *
                       "$(record.bits) bits$(record.signs_sufficient ? "" : ", signs not determined")$(record.valid ? "" : ", INVALID")" :
                       "error: $(record.error)", ", ", round(time() - t0, digits = 1), " s")
    if interrupted
      verbose && println("interrupted: sample $n recorded as skipped; rerun to continue with the next curve")
      break
    end
  end
  verbose && println("summary: ", join(["$k: $v" for (k, v) in tallies], ", "))
  return results
end

@doc raw"""
    load_theta_data(files; kinds = nothing, types = nothing, valid_only = true) -> Vector{Dict{Symbol, Any}}

The samples of sample_theta_data in a file or a list of files (status :ok,
each curve once; by default only the valid ones; optionally only those of
the given kinds or types): every field as a string except index, seed, prec,
bits (Int), accola_log2 (Float64), kind, type, verdict, stage (Symbol) and
thetas (a dictionary even characteristic => AcbFieldElem at precision bits,
exact midpoints).
"""
function load_theta_data(files; kinds = nothing, types = nothing, valid_only::Bool = true)
  chars = even_theta_characteristics(5)
  samples = Dict{Symbol, Any}[]
  seen = Set{String}()
  for file in (files isa AbstractString ? [files] : files), line in eachline(file)
    startswith(line, "sample") || continue
    d = Dict{Symbol, Any}()
    for field in split(line, "\t")[2:end]
      k, v = split(field, "="; limit = 2)
      d[Symbol(k)] = v
    end
    d[:status] == "ok" || continue
    valid_only && get(d, :valid, "true") != "true" && continue
    d[:curve] in seen && continue
    push!(seen, d[:curve])
    for k in (:index, :seed, :prec, :bits)
      d[k] = parse(Int, d[k])
    end
    d[:accola_log2] = parse(Float64, d[:accola_log2])
    for k in (:kind, :type, :verdict, :stage)
      d[k] = Symbol(d[k])
    end
    kinds === nothing || d[:kind] in kinds || continue
    types === nothing || d[:type] in types || continue
    CC = AcbField(d[:bits])
    RR = ArbField(d[:bits])
    thetas = Dict{NTuple{10, Int}, AcbFieldElem}()
    setprecision(BigFloat, d[:bits] + 16) do
      for (c, entry) in zip(chars, split(d[:thetas], ";"))
        re, im = split(entry, ",")
        thetas[Tuple(c)] = CC(RR(parse(BigFloat, re)), RR(parse(BigFloat, im)))
      end
    end
    d[:thetas] = thetas
    push!(samples, d)
  end
  return samples
end

################################################################################
#
#  Approaching special points of the Schottky locus (hyperelliptic Jacobians,
#  products of Jacobians)
#
################################################################################

@doc raw"""
    product_degeneration_direction(partition; seed = 1) -> Matrix{ComplexF64}

A first order direction from a product of Jacobians of dimensions
`partition` (block diagonal period matrix) into J_g: smoothing the nodes of
a chain of curves C_1 - C_2 - ... gives off-diagonal blocks u_i v_{i+1}^T
between consecutive blocks to first order in the smoothing parameter (u_i,
v_{i+1} the values of the differentials at the two points of the node;
random here), symmetric, normalized to largest entry 1.
"""
function product_degeneration_direction(partition::Vector{Int}; seed::Int = 1)
  rng = Random.MersenneTwister(seed)
  g = sum(partition)
  D = zeros(ComplexF64, g, g)
  offsets = cumsum([0; partition])
  for i in 1:length(partition)-1
    u, v = randn(rng, ComplexF64, partition[i]), randn(rng, ComplexF64, partition[i + 1])
    block = u * transpose(v)
    rows, cols = offsets[i]+1:offsets[i+1], offsets[i+1]+1:offsets[i+2]
    D[rows, cols] = block
    D[cols, rows] = transpose(block)
  end
  return D / maximum(abs, D)
end

function _evidence_summary(e)
  parts = String[]
  r(x) = round(x, digits = 1)
  haskey(e, :vanishing_theta_constants) && push!(parts, "vanishing $(e.vanishing_theta_constants)")
  haskey(e, :schottky_jung_rank) && push!(parts, "SJ $(e.schottky_jung_rank)/$(e.schottky_jung_needed)")
  haskey(e, :gradient_residual) && push!(parts, "Fay 2^$(r(e.gradient_residual))")
  haskey(e, :prym_gradient_residual) && push!(parts, "Prym Fay 2^$(r(e.prym_gradient_residual))")
  haskey(e, :squares_singular_values_log2) &&
    push!(parts, "squares min 2^$(r(minimum(e.squares_singular_values_log2)))")
  haskey(e, :quadric_singular_values_log2) &&
    push!(parts, "quadric sv 2^$(r.(e.quadric_singular_values_log2[1:min(8, end)]))")
  for k in (:schottky_jung_error, :gradient_kernel_error, :prym_gradient_kernel_error)
    haskey(e, k) && push!(parts, "$k: $(first(e[k], 100))")
  end
  return join(parts, ", ")
end

@doc raw"""
    approach_point(S, tau0, ts; direction = nothing, seed = 1, prec = 1024, classify_prec = nothing,
                   codimension = nothing, max_iterations = 60, sign_data = nothing,
                   verbose = true) -> NamedTuple

How the zero locus of S (e.g. accola_system(product = true): at points
where theta constants vanish the default signed sums of Accola's equations
are not differentiable, the products are) and the classification
behave near a special point tau0 of J_g (a hyperelliptic Jacobian, a product
of Jacobians): first the local structure at tau0 (residual, singular values
of the Jacobian of S there: the local codimension of the zero locus, which
may be singular at tau0), then for each t in `ts` (e.g. 2.0 .^ -(2:4:40))
the point tau0 + t D (D = `direction`, a complex symmetric matrix, e.g.
product_degeneration_direction for a product; default random, largest
entry 1) projected onto the zero locus (project_to_locus), the distance of
the projection to tau0 and to tau0 + t D (log2), its rank, and
classify_jacobian of it (allow_vanishing; at classify_prec, default
prec - 80) with the evidence: how the quantities of the classification
(Fay residuals, squares, quadric singular values) behave as t -> 0.
Without `project` the points tau0 + t D themselves are classified, at
about 2 log2(1/t) bits: for a first order family in J_g such as
compact_type_degeneration (Fay), which is a Jacobian up to O(t^2) (no
projection needed; use t well below 2^-(the bits wanted / 2)); with
`local_structure = false` the step at tau0 is skipped.

Returns (local, results).
"""
function approach_point(S::ThetaEquationSystem, tau0::AcbMatrix, ts; direction = nothing, seed::Int = 1,
                        prec::Int = 1024, classify_prec = nothing, codimension = nothing,
                        max_iterations::Int = 60, sign_data = nothing, project::Bool = true,
                        local_structure::Bool = true, verbose::Bool = true)
  g = nrows(tau0)
  CC = AcbField(prec)
  t0 = _change_precision(tau0, CC)
  coordinates = _upper_coordinates(g)
  if direction === nothing
    rng = Random.MersenneTwister(seed)
    direction = zeros(ComplexF64, g, g)
    for (i, j) in coordinates
      direction[i, j] = direction[j, i] = randn(rng, ComplexF64)
    end
    direction /= maximum(abs, direction)
  end
  # the local structure of the zero locus at tau0
  values, states = local_structure ? _system_residual(S, _change_precision(t0, AcbField(256)), nothing) :
                                     (AcbFieldElem[], nothing)
  local_data = !local_structure ? (residual_log2 = NaN, error = "not computed") : try
    decomposition = RSR.LinearAlgebra.svd(residual_jacobian(S, t0, states); full = true)
    (residual_log2 = round(_max_log2(values), digits = 1),
     singular_values_log2 = round.(RSR._safe_log2.(decomposition.S), digits = 1),
     rank = _numerical_rank(decomposition.S))
  catch err
    err isa InterruptException && rethrow()
    (residual_log2 = round(_max_log2(values), digits = 1), error = sprint(showerror, err))
  end
  verbose && println("at tau0: residual 2^$(local_data.residual_log2), ",
                     hasproperty(local_data, :error) ? local_data.error :
                     "Jacobian singular values 2^$(local_data.singular_values_log2) (rank $(local_data.rank))")
  pairs_prym = _loaded_sign_data(sign_data, g - 1)
  cprec = classify_prec === nothing ? prec - 80 : classify_prec
  distance_log2(A, B) = maximum(RSR._safe_log2(RSR._abs64(A[i, j] - B[i, j])) for (i, j) in coordinates)
  results = NamedTuple[]
  for t in ts
    clock = time()
    start = deepcopy(t0)
    for (i, j) in coordinates
      _add_symmetric!(start, i, j, direction isa AcbMatrix ? CC(t) * CC(direction[i, j]) :
                                   CC(real(t * direction[i, j]), imag(t * direction[i, j])))
    end
    # without projection (a first order family in J_g, e.g.
    # compact_type_degeneration): the point is a Jacobian up to O(t^2), so
    # it is classified at about 2 log2(1/t) bits
    tprec = project ? cprec : (classify_prec === nothing ? min(prec - 80, floor(Int, -2 * log2(t)) - 32) : classify_prec)
    record = try
      p = project ? project_to_locus(S, start; prec = prec, max_iterations = max_iterations, codimension = codimension) :
                    (tau = start, status = :converged, residual_log2 = NaN, rank = 0, singular_values_log2 = Float64[])
      verdict, stage, evidence, smallest = :none, :none, nothing, Float64[]
      if p.status === :converged
        tc = _change_precision(p.tau, AcbField(tprec))
        thetas = Hecke.thetas([zero(base_ring(tc)) for _ in 1:g], tc)
        evens = [v for (k, v) in thetas if RSR._is_even(k)]
        largest = maximum(RSR._safe_log2(RSR._abs64(v)) for v in evens)
        smallest = round.(sort([RSR._safe_log2(RSR._abs64(v)) - largest for v in evens])[1:12], digits = 1)
        c = classify_jacobian(g, thetas; sign_data = pairs_prym, allow_vanishing = true)
        verdict, stage, evidence = c.verdict, c.stage, c.evidence
      end
      (t = t, status = p.status, residual_log2 = round(p.residual_log2, digits = 1),
       distance_to_tau0_log2 = round(distance_log2(p.tau, t0), digits = 1),
       moved_log2 = round(distance_log2(p.tau, start), digits = 1), rank = p.rank,
       singular_values_log2 = round.(p.singular_values_log2, digits = 1),
       verdict = verdict, stage = stage, classify_prec = tprec, smallest_thetas_log2 = smallest,
       evidence = evidence, tau = p.tau)
    catch err
      err isa InterruptException && rethrow()
      (t = t, status = :error, error = sprint(showerror, err))
    end
    push!(results, record)
    if verbose
      if record.status === :error
        println("t = 2^$(round(log2(t), digits = 1)): error ", record.error)
      else
        println("t = 2^$(round(log2(t), digits = 1)): $(record.status), residual 2^$(record.residual_log2), ",
                "distance to tau0 2^$(record.distance_to_tau0_log2), moved 2^$(record.moved_log2), rank $(record.rank), ",
                "$(record.verdict) ($(record.stage)) at $(record.classify_prec) bits, ", round(time() - clock, digits = 1), " s")
        isempty(record.smallest_thetas_log2) || println("    smallest even thetas 2^", record.smallest_thetas_log2)
        record.evidence === nothing || println("    ", _evidence_summary(record.evidence))
      end
    end
  end
  return (local_data = local_data, results = results)
end

################################################################################
#
#  The quadric count as a determinantal condition
#
#  For the odd characteristics d of the Prym (with their lifts (i1, i2), see
#  lift_prym_indices) the matrix M = [S | P]: S[d, :] the square of the
#  gradient of the Prym (quadratic monomials in g - 1 variables), P[d, :] the
#  symmetrized product of the gradients of the lifts (quadratic monomials in
#  g variables). The quadrics of _quadrics_from_gradients are the row space of
#  O^T P with O the left kernel of S, so (S of full rank) their number is
#  rank(M) - rank(S): for g = 5 a Jacobian has rank(M) = 10 + 3 = 13, an
#  intermediate Jacobian 10 + 5 = 15. The Jacobians satisfy: all 14 x 14
#  minors of M vanish. The rank does not depend on the bases of the gradients
#  (GL_g, GL_(g-1)) nor on the scaling of the rows.
#
################################################################################

_lower_monomials(n::Int) = [(i, j) for j in 1:n for i in j:n]

# x scaled by 2^-e in place
_scale_2exp!(x::AcbFieldElem, e::Int) = RSR._acb_mul_2exp!(x, x, -e)
_exponent_of(x::Float64) = x > 0 ? round(Int, log2(x)) : 0

@doc raw"""
    gradient_rank_matrix(g, thetas; sign_data = nothing, fay_relations = nothing,
                         prym_fay_relations = nothing, rhos = nothing, prym_rhos = nothing)
      -> NamedTuple

The matrix M = [S | P] (see above) for the theta constants `thetas` of genus g
(even characteristics; the Prym by Schottky-Jung with the signs from
Riemann's relations, `sign_data` of genus g - 1), the gradients from the Fay
kernels. Each block and then each row is scaled by a power of 2 to largest
entry about 1. Returns (M, prym_columns (the number of columns of S), pairs
(the lifts, the rows), K, K_prym, thetas_prym (the theta constants of the
Prym used for K_prym)).
"""
function gradient_rank_matrix(g::Int, thetas; sign_data = nothing, fay_relations = nothing,
                              prym_fay_relations = nothing, rhos = nothing, prym_rhos = nothing)
  CC = parent(first(values(thetas)))
  th = Dict{NTuple{2*g, Int}, AcbFieldElem}(Tuple(k) => v for (k, v) in thetas)
  for c in odd_theta_characteristics(g)
    haskey(th, Tuple(c)) || (th[Tuple(c)] = zero(CC))
  end
  thetas_prym = prym_thetas(g, th)
  correct_signs_with_data!(thetas_prym, g - 1, _loaded_sign_data(sign_data, g - 1); fallback = true)
  K, _ = odd_theta_gradient_kernel(g, th; rhos = rhos, relations = fay_relations)
  Kp, _ = odd_theta_gradient_kernel(g - 1, thetas_prym; rhos = prym_rhos, relations = prym_fay_relations)
  CC = base_ring(K)
  pairs = RSR.lift_prym_indices(g)
  a, b = length(_lower_monomials(g - 1)), length(_lower_monomials(g))
  n = length(pairs)
  M = zero_matrix(CC, n, a + b)
  for (d, (i1, i2)) in enumerate(pairs)
    for (k, (x, y)) in enumerate(_lower_monomials(g - 1))
      M[d, k] = Kp[d, x] * Kp[d, y]
    end
    for (k, (x, y)) in enumerate(_lower_monomials(g))
      M[d, a + k] = K[i1, x] * K[i2, y] + K[i2, x] * K[i1, y]
    end
  end
  for cols in (1:a, a+1:a+b)
    e = _exponent_of(maximum(RSR._abs64(M[i, j]) for i in 1:n for j in cols))
    for i in 1:n, j in cols
      x = M[i, j]; _scale_2exp!(x, e); M[i, j] = x
    end
  end
  for i in 1:n
    e = _exponent_of(maximum(RSR._abs64(M[i, j]) for j in 1:a+b))
    for j in 1:a+b
      x = M[i, j]; _scale_2exp!(x, e); M[i, j] = x
    end
  end
  return (M = M, prym_columns = a, pairs = pairs, K = K, K_prym = Kp, thetas_prym = thetas_prym)
end

@doc raw"""
    determinantal_data(samples; sign_data = nothing, verbose = true) -> Vector{NamedTuple}

For samples of load_theta_data (dictionaries with :thetas, :type, :bits,
...): gradient_rank_matrix and the singular values (log2, decreasing) of M,
the numerical rank (above -bits/2) and of S. Prints per sample the type, the
rank of M and the singular values around the expected gap (positions 11 to
17). Samples where the gradients fail are skipped (reported).
"""
function determinantal_data(samples; sign_data = nothing, verbose::Bool = true)
  data4 = _loaded_sign_data(sign_data, 4)
  out = NamedTuple[]
  for s in samples
    clock = time()
    r = try
      gradient_rank_matrix(5, s[:thetas]; sign_data = data4)
    catch err
      err isa InterruptException && rethrow()
      verbose && println("$(s[:type]) $(get(s, :index, "")): error ", first(sprint(showerror, err), 150))
      continue
    end
    sv = singular_values_log2(r.M)
    S = matrix(base_ring(r.M), nrows(r.M), r.prym_columns, [r.M[i, j] for i in 1:nrows(r.M) for j in 1:r.prym_columns])
    svS = singular_values_log2(S)
    bits = s[:bits]
    rank = count(>(-bits / 2), sv)
    rankS = count(>(-bits / 2), svS)
    push!(out, (type = s[:type], index = get(s, :index, 0), bits = bits, M = r.M, prym_columns = r.prym_columns,
                singular_values_log2 = sv, rank = rank, rank_S = rankS))
    verbose && println(rpad(string(s[:type]), 24), " rank M $rank (S $rankS); singular values 11-17: 2^",
                       round.(sv[11:min(17, end)], digits = 1), " ", round(time() - clock, digits = 1), " s")
  end
  return out
end

# log2 |det| of the submatrix of M (rows, cols), its rows scaled to largest
# entry about 1 (so that the value is comparable between samples)
function _minor_log2(M::AcbMatrix, rows, cols)
  A = matrix(base_ring(M), length(rows), length(cols), [M[i, j] for i in rows for j in cols])
  for i in 1:nrows(A)
    e = _exponent_of(maximum(RSR._abs64(A[i, j]) for j in 1:ncols(A)))
    for j in 1:ncols(A)
      x = A[i, j]; _scale_2exp!(x, e); A[i, j] = x
    end
  end
  return RSR._safe_log2(RSR._abs64(det(A)))
end

@doc raw"""
    minor_certificates(data; size = 14, tries = 200, seed = 1, columns = :random,
                       verbose = true) -> NamedTuple

Searches minors of M (determinantal_data) that separate the Jacobians from
the other samples: random sets of `size` rows (characteristics of the Prym)
and `size` columns (`columns = :random`; `:prym`: all columns of S and the
rest of P), the minor (rows scaled) on every sample. A certificate vanishes
on all Jacobians (below -bits/2) and not on the other samples (above
-bits/4). Prints the counts and the margins; returns (certificates (rows,
cols, largest log2 on the Jacobians, smallest on the others), tried).
"""
function minor_certificates(data; size::Int = 14, tries::Int = 200, seed::Int = 1, columns::Symbol = :random,
                            verbose::Bool = true)
  rng = Random.MersenneTwister(seed)
  jac = [x for x in data if x.type === :jacobian]
  other = [x for x in data if x.type !== :jacobian]
  @req !isempty(jac) && !isempty(other) "Need Jacobians and other samples."
  n, m = nrows(jac[1].M), ncols(jac[1].M)
  a = jac[1].prym_columns
  certificates = NamedTuple[]
  failed_jacobian, failed_other = 0, 0
  for _ in 1:tries
    rows = sort(Random.randperm(rng, n)[1:size])
    cols = columns === :prym ? sort([collect(1:a); a .+ Random.randperm(rng, m - a)[1:size - a]]) :
                               sort(Random.randperm(rng, m)[1:size])
    vj = [_minor_log2(x.M, rows, cols) + x.bits / 2 for x in jac]      # < 0: vanishing
    vo = [_minor_log2(x.M, rows, cols) + x.bits / 4 for x in other]    # > 0: not vanishing
    if maximum(vj) >= 0
      failed_jacobian += 1
    elseif minimum(vo) <= 0
      failed_other += 1
    else
      push!(certificates, (rows = rows, cols = cols,
                           jacobian_log2 = round(maximum(_minor_log2(x.M, rows, cols) for x in jac), digits = 1),
                           other_log2 = round(minimum(_minor_log2(x.M, rows, cols) for x in other), digits = 1)))
    end
  end
  if verbose
    println("$tries tried: $(length(certificates)) certificates, $failed_jacobian not vanishing on all Jacobians, ",
            "$failed_other vanishing on some other sample")
    if !isempty(certificates)
      println("largest log2 |minor| on the Jacobians: ", maximum(c.jacobian_log2 for c in certificates),
              "; smallest on the others: ", minimum(c.other_log2 for c in certificates))
    end
  end
  return (certificates = certificates, tried = tries)
end

################################################################################
#
#  Brackets of gradients (Jacobian nullwerte) and theta constants
#
#  The minors of M are invariants of GL_g x GL_(g-1), i.e. polynomials in the
#  brackets [d_1 ... d_g] = det of g gradients of odd theta functions (the
#  Jacobian nullwerte, for the curve and for the Prym). The gradients are
#  known up to GL_g only, so a single bracket is known up to a factor common
#  to all brackets of the sample, ratios of brackets exactly. Test: is the
#  ratio of two brackets (in absolute value) a monomial in the even theta
#  constants, i.e. log |ratio| an integral (or half-integral) combination of
#  the log |theta|, the same for all samples?
#
################################################################################

@doc raw"""
    gradient_samples(samples; sign_data = nothing, verbose = true) -> Vector{NamedTuple}

For samples of load_theta_data: the gradients of the curve (K, rows
odd_theta_characteristics(5)) and of the Prym (K_prym, rows
odd_theta_characteristics(4)) as ComplexF64 matrices, log |theta| and theta
(ComplexF64) at even_theta_characteristics(5), the theta constants of the
Prym (thetas_prym, at even_theta_characteristics(4)) and the type.
"""
function gradient_samples(samples; sign_data = nothing, verbose::Bool = true)
  data4 = _loaded_sign_data(sign_data, 4)
  evens = [Tuple(c) for c in even_theta_characteristics(5)]
  evens_prym = [Tuple(c) for c in even_theta_characteristics(4)]
  out = NamedTuple[]
  for (n, s) in enumerate(samples)
    r = try
      gradient_rank_matrix(5, s[:thetas]; sign_data = data4)
    catch err
      err isa InterruptException && rethrow()
      verbose && println("sample $n: error ", first(sprint(showerror, err), 120))
      continue
    end
    to64(A) = [RSR._c64(A[i, j]) for i in 1:nrows(A), j in 1:ncols(A)]
    logs = [log(RSR._abs64(s[:thetas][e])) for e in evens]
    push!(out, (type = s[:type], K = to64(r.K), K_prym = to64(r.K_prym), log_thetas = logs,
                thetas = [RSR._c64(s[:thetas][e]) for e in evens],
                thetas_prym = [RSR._c64(r.thetas_prym[e]) for e in evens_prym]))
    verbose && n % 10 == 0 && println("$n samples done")
  end
  return out
end

@doc raw"""
    random_bracket_pairs(g, count; seed = 1, shared = g - 1) -> Vector

`count` pairs (S, T) of g-sets of indices of odd characteristics of genus g
(rows of K, resp. K_prym for g - 1) with `shared` elements in common (g - 1:
brackets that differ in one gradient). With `azygetic` all characteristics
of S and T together form an azygetic set (_azygetic: for odd
characteristics, every three have an even sum), the configurations of
Jacobi's derivative formula and its generalizations (fundamental_completions).
"""
function random_bracket_pairs(g::Int, count::Int; seed::Int = 1, shared::Int = g - 1, azygetic::Bool = false)
  rng = Random.MersenneTwister(seed)
  odds = [collect(c) for c in odd_theta_characteristics(g)]
  n = length(odds)
  azygetic_triple(i, j, k) = _azygetic(odds[i], odds[j], odds[k], g)
  function azygetic_set(m)
    # greedily, from a random start (restarted when stuck)
    while true
      chosen = [rand(rng, 1:n)]
      for i in Random.randperm(rng, n)
        i in chosen && continue
        all(azygetic_triple(i, j, k) for j in chosen for k in chosen if j < k) || continue
        push!(chosen, i)
        length(chosen) == m && return chosen
      end
    end
  end
  pairs = Tuple{Vector{Int}, Vector{Int}}[]
  while length(pairs) < count
    p = azygetic ? azygetic_set(2*g - shared) : Random.randperm(rng, n)
    common = p[1:shared]
    S = sort([common; p[shared+1:g]])
    T = sort([common; p[g+1:2*g-shared]])
    push!(pairs, (S, T))
  end
  return pairs
end

# least squares (with a constant column) of r on the columns of L restricted
# to `support`; returns the coefficients and the relative residual
function _fit_on(L::Matrix{Float64}, r::Vector{Float64}, support::Vector{Int})
  A = [L[:, support] ones(size(L, 1))]
  x = A \ r
  return x, RSR.LinearAlgebra.norm(A * x - r) / max(RSR.LinearAlgebra.norm(r), 1e-300)
end

@doc raw"""
    bracket_monomial_test(gs, pairs; side = :curve, max_terms = 32, tolerance = 1e-9,
                          verbose = true) -> Vector{NamedTuple}

For each pair (S, T) (random_bracket_pairs) the ratio of the brackets
det K[S, :] / det K[T, :] (`side = :curve`; `:prym`: K_prym, sets of 4) on the
Jacobians among gs (gradient_samples): is log |ratio| a combination of the
log |theta| (even characteristics; plus a constant) with half-integral
coefficients, the same on all samples? With more samples than even theta
constants (528) by least squares on all of them, otherwise greedily (the
theta constant that explains most of the residual, refitted, up to
`max_terms`). The coefficients are rounded to halves and the residual of
the rounded monomial is checked on the Jacobians and on the other samples
(for an identity of all principally polarized abelian varieties it holds
there too). Prints per pair the number of terms, the residuals and the
monomial (characteristics with exponents).
"""
function bracket_monomial_test(gs, pairs; side::Symbol = :curve, max_terms::Int = 32,
                               tolerance::Float64 = 1e-9, verbose::Bool = true)
  LA = RSR.LinearAlgebra
  jac = [x for x in gs if x.type === :jacobian]
  other = [x for x in gs if x.type !== :jacobian]
  evens = [Tuple(c) for c in even_theta_characteristics(5)]
  L = reduce(vcat, [transpose(x.log_thetas) for x in jac])
  Lo = isempty(other) ? zeros(0, length(evens)) : reduce(vcat, [transpose(x.log_thetas) for x in other])
  N, E = size(L)
  bracket(x, S) = side === :curve ? LA.det(x.K[S, :]) : LA.det(x.K_prym[S, :])
  logratio(x, S, T) = log(abs(bracket(x, S))) - log(abs(bracket(x, T)))
  results = NamedTuple[]
  for (S, T) in pairs
    r = [logratio(x, S, T) for x in jac]
    if N > E + 1
      support = collect(1:E)
      x, res = _fit_on(L, r, support)
    else
      support = Int[]
      x, res = _fit_on(L, r, support)
      norms = [LA.norm(L[:, e]) for e in 1:E]
      while res > tolerance && length(support) < min(max_terms, N - 2)
        residual = r - [L[:, support] ones(N)] * x
        scores = [e in support ? -1.0 : abs(LA.dot(L[:, e], residual)) / norms[e] for e in 1:E]
        push!(support, argmax(scores))
        x, res = _fit_on(L, r, support)
      end
    end
    exps = round.(2 .* x[1:end-1]) ./ 2
    keep = findall(!iszero, exps)
    sup, ex = support[keep], exps[keep]
    # the rounded monomial (the constant refitted)
    constant = isempty(jac) ? 0.0 : sum(r .- L[:, sup] * ex) / N
    rounded_res = LA.norm(L[:, sup] * ex .+ constant .- r) / max(LA.norm(r), 1e-300)
    other_res = isempty(other) ? NaN :
                begin
                  ro = [logratio(x, S, T) for x in other]
                  LA.norm(Lo[:, sup] * ex .+ constant .- ro) / max(LA.norm(ro), 1e-300)
                end
    monomial = [(evens[e], c) for (e, c) in zip(sup, ex)]
    push!(results, (S = S, T = T, fit_residual = res, rounded_residual = rounded_res, other_residual = other_res,
                    constant = constant, monomial = monomial))
    if verbose
      println("S = $S, T = $T: $(length(sup)) terms, fit residual $(round(log10(max(res, 1e-300)), digits = 1)), ",
              "rounded $(round(log10(max(rounded_res, 1e-300)), digits = 1)), other samples ",
              isnan(other_res) ? "-" : round(log10(max(other_res, 1e-300)), digits = 1),
              ", constant exp $(round(exp(constant), sigdigits = 6))")
      rounded_res < 1e-8 && println("    ", join(["θ[$(join(c))]^$e" for (c, e) in monomial], " "))
    end
  end
  return results
end

################################################################################
#
#  Jacobian nullwerte as sums over fundamental systems
#
#  Igusa (On Jacobi's derivative formula and its generalizations, 1980): for
#  g <= 5 and an azygetic set n_1, ..., n_g of odd characteristics the
#  Jacobian nullwert D(n_1, ..., n_g) = det(d theta[n_i] / d z_j (0)) is a
#  polynomial of degree g + 2 in the theta constants, supported on the
#  products theta[m_1] ... theta[m_(g+2)] with {n, m} a fundamental system
#  (azygetic, 2g + 2 characteristics, sum 0). The number of such completions
#  by even characteristics is 1 for g <= 3 (Jacobi, Rosenhain, Thomae /
#  Frobenius: a monomial), 2 for g = 4 and 8 for g = 5. The gradients K are
#  known up to GL_g, so D(S) = c P_S(theta) with c common to all S of a sample:
#  for a pair (S, T) the vector of coefficients of (P_S, P_T) is in the kernel
#  of the rows D(T) theta^m (m completing S), -D(S) theta^m' (m' completing T),
#  one row per sample.
#
################################################################################

# characteristics as bit masks: bit i - 1 is entry i of (a_1, ..., a_g, b_1, ..., b_g)
function _char_mask(c)
  m = 0
  for (i, x) in enumerate(c)
    isodd(x) && (m |= 1 << (i - 1))
  end
  return m
end

# the parity a . b mod 2 of a mask
_mask_parity(m::Int, g::Int) = isodd(count_ones(m & (m >> g) & ((1 << g) - 1)))

# Igusa: m1, m2, m3 azygetic iff e(m1) e(m2) e(m3) e(m1 + m2 + m3) = -1
_azygetic_masks(a::Int, b::Int, c::Int, g::Int) =
  isodd(_mask_parity(a, g) + _mask_parity(b, g) + _mask_parity(c, g) + _mask_parity(a ⊻ b ⊻ c, g))

_azygetic(a, b, c, g::Int) = _azygetic_masks(_char_mask(a), _char_mask(b), _char_mask(c), g)

_odd_masks(g::Int) = [_char_mask(c) for c in odd_theta_characteristics(g)]
_even_masks(g::Int) = [_char_mask(c) for c in even_theta_characteristics(g)]

# the pairs (v[i], v[j]), i < j
_pairs_of(v) = [(v[i], v[j]) for j in eachindex(v) for i in 1:j-1]

@doc raw"""
    fundamental_completions(g, S) -> Vector{Vector{Int}}

For S indices into odd_theta_characteristics(g) of an azygetic set of g odd
characteristics: all sets of g + 2 even characteristics (indices into
even_theta_characteristics(g)) that complete S to an azygetic set of 2g + 2
characteristics (a fundamental system; their sum is checked to be 0).
"""
fundamental_completions(g::Int, S::Vector{Int}) = _fundamental_completions(g, _odd_masks(g)[S], _even_masks(g))

function _fundamental_completions(g::Int, n::Vector{Int}, evens::Vector{Int})
  az(a, b, c) = _azygetic_masks(a, b, c, g)
  @req all(az(a, b, c) for (a, b) in _pairs_of(n) for c in n if c != a && c != b) "The characteristics are not azygetic."
  candidates = [e for e in eachindex(evens) if all(az(a, b, evens[e]) for (a, b) in _pairs_of(n))]
  out = Vector{Int}[]
  current = Int[]
  function extend(start)
    if length(current) == g + 2
      push!(out, copy(current))
      return
    end
    for t in start:length(candidates)
      m = evens[candidates[t]]
      all(az(a, evens[e], m) for a in n for e in current) || continue
      all(az(evens[a], evens[b], m) for (a, b) in _pairs_of(current)) || continue
      push!(current, candidates[t])
      extend(t + 1)
      pop!(current)
    end
  end
  extend(1)
  for c in out
    @assert iszero(reduce(⊻, n) ⊻ reduce(⊻, evens[c])) "completion with nonzero sum"
  end
  return out
end

@doc raw"""
    bracket_kernel_test(gs, pairs; side = :curve, verbose = true) -> Vector{NamedTuple}

For each pair (S, T) of azygetic sets (random_bracket_pairs(g, count;
azygetic = true), g = 5 for `side = :curve`, 4 for `:prym`) and the samples
gs (gradient_samples, with complex theta constants): is the ratio of the
brackets D(S) / D(T) equal to P_S(theta) / P_T(theta), with P_S a combination
of the monomials theta[m_1] ... theta[m_(g+2)] over the fundamental
completions of S (fundamental_completions)? The coefficients are the kernel
of one row per Jacobian (normalized); printed: the number of completions, the
three smallest singular values (log10, relative to the largest), the kernel
vector scaled to first entry 1 (rounded to 3 digits; Igusa: all +-1) and
the residual of that vector on the other samples (the identity holds on all
of A_g, so also on intermediate Jacobians).
"""
function bracket_kernel_test(gs, pairs; side::Symbol = :curve, verbose::Bool = true)
  LA = RSR.LinearAlgebra
  @req side in (:curve, :prym) "side is :curve or :prym"
  @req all(x -> hasproperty(x, :thetas), gs) "Recompute gs with the current gradient_samples (complex theta constants)."
  g = side === :curve ? 5 : 4
  jac = [x for x in gs if x.type === :jacobian]
  other = [x for x in gs if x.type !== :jacobian]
  gradients(x) = side === :curve ? x.K : x.K_prym
  theta_values(x) = side === :curve ? x.thetas : x.thetas_prym
  bracket(x, S) = LA.det(gradients(x)[S, :])
  monomials(x, C) = [prod(theta_values(x)[c]) for c in C]
  function row(x, S, T, CS, CT)
    r = [bracket(x, T) .* monomials(x, CS); -bracket(x, S) .* monomials(x, CT)]
    return r ./ LA.norm(r)
  end
  results = NamedTuple[]
  for (S, T) in pairs
    CS, CT = fundamental_completions(g, S), fundamental_completions(g, T)
    A = reduce(vcat, [transpose(row(x, S, T, CS, CT)) for x in jac])
    F = LA.svd(A; full = true)
    sv = F.S ./ F.S[1]
    v = conj.(F.Vt[end, :])
    if size(A, 1) < size(A, 2)
      verbose && println("S = $S, T = $T: only $(size(A, 1)) Jacobians for $(size(A, 2)) unknowns")
    end
    kernel_residual = LA.norm(A * v)
    v = v ./ v[1]
    other_residual = isempty(other) ? NaN :
                     maximum(abs(LA.dot(conj.(row(x, S, T, CS, CT)), v)) / LA.norm(v) for x in other)
    smallest = round.(log10.(max.(sv[max(1, end - 2):end], 1e-300)), digits = 1)
    push!(results, (S = S, T = T, completions_S = CS, completions_T = CT, singular_values = sv,
                    coefficients = v, kernel_residual = kernel_residual, other_residual = other_residual))
    if verbose
      println("S = $S, T = $T: $(length(CS)) + $(length(CT)) completions, smallest singular values 10^$smallest, ",
              "other samples 10^", isnan(other_residual) ? "-" : round(log10(max(other_residual, 1e-300)), digits = 1))
      println("    coefficients ", join([string(round(real(c), digits = 3), imag(c) < 0 ? " - " : " + ",
                                                round(abs(imag(c)), digits = 3), "i") for c in v], ", "))
    end
  end
  return results
end

################################################################################
#
#  The gradients from the theta constants
#
#  With Igusa's formula every azygetic bracket is c P_S(theta). For a basis B
#  (g odd characteristics, azygetic) and x with B + x azygetic, Cramer's rule
#  gives the gradient of theta[x] in the basis of the gradients of B:
#  x = sum_j D(B with b_j replaced by x) / D(B) b_j, a ratio of theta
#  polynomials. azygetic_basis_chain finds bases that reach all odd
#  characteristics from a reference basis (two rounds in genus 4 and 5), so
#  the gradients up to GL_g, the matrix K, are rational functions of the theta
#  constants: theta_gradient_rows. The signs of the sums are learned from
#  samples (bracket_sign_table).
#
################################################################################

@doc raw"""
    azygetic_basis_chain(g; seed = 1, reference = nothing) -> NamedTuple

A reference basis (sorted indices into odd_theta_characteristics(g), an
azygetic set of g odd characteristics; random unless given) and, for every other odd
characteristic x in `order`, a basis `bases[x]` (sorted) of characteristics
earlier in the order (or of the reference) such that the basis and x together
are azygetic. Random (seeded) depth first search, in rounds.
"""
function azygetic_basis_chain(g::Int; seed::Int = 1, reference = nothing)
  rng = Random.MersenneTwister(seed)
  odds = _odd_masks(g)
  n = length(odds)
  az(i, j, k) = _azygetic_masks(odds[i], odds[j], odds[k], g)
  # g elements of `known` that are azygetic together with x
  function basis_for(x, known)
    candidates = Random.shuffle(rng, [y for y in known if y != x])
    current = Int[]
    function extend(start)
      length(current) == g && return true
      for t in start:length(candidates)
        y = candidates[t]
        all(az(a, b, y) for (a, b) in _pairs_of([x; current])) || continue
        push!(current, y)
        extend(t + 1) && return true
        pop!(current)
      end
      return false
    end
    return extend(1) ? sort(current) : nothing
  end
  if reference === nothing
    reference = basis_for(rand(rng, 1:n), collect(1:n))
  else
    reference = sort(collect(reference))
    @req length(reference) == g && all(az(a, b, c) for (a, b) in _pairs_of(reference) for c in reference
                                        if c != a && c != b) "The reference is not an azygetic set of g odd characteristics."
  end
  known = Set(reference)
  order = Int[]
  bases = Dict{Int, Vector{Int}}()
  while length(known) < n
    previous = sort(collect(known))
    new = Int[]
    for x in 1:n
      x in known && continue
      B = basis_for(x, previous)
      B === nothing && continue
      push!(new, x)
      bases[x] = B
    end
    @req !isempty(new) "No azygetic bases reach the remaining odd characteristics."
    append!(order, new)
    union!(known, new)
  end
  return (reference = reference, order = order, bases = bases)
end

# The sorted azygetic sets whose brackets theta_gradient_rows needs.
function _chain_bracket_sets(chain)
  sets = Set{Vector{Int}}([chain.reference])
  for x in chain.order
    B = chain.bases[x]
    push!(sets, B)
    for j in eachindex(B)
      push!(sets, sort([B[1:j-1]; x; B[j+1:end]]))
    end
  end
  return sort(collect(sets))
end

_permutation_sign(v) = iseven(count(v[i] > v[j] for j in eachindex(v) for i in 1:j-1)) ? 1 : -1

# sum_m e_m theta^m over the completions
function _igusa_sum(theta_values::AbstractVector, completions, signs)
  s = zero(theta_values[1])
  for (c, e) in zip(completions, signs)
    s += e * prod(theta_values[c])
  end
  return s
end

_side_genus(side::Symbol) = (@req side in (:curve, :prym) "side is :curve or :prym"; side === :curve ? 5 : 4)
_side_gradients(x, side::Symbol) = side === :curve ? x.K : x.K_prym
_side_thetas(x, side::Symbol) = side === :curve ? x.thetas : x.thetas_prym

@doc raw"""
    bracket_sign_table(gs, sets; side = :curve, reference = first(sets), verbose = true) -> NamedTuple

For sorted azygetic g-sets (indices into odd_theta_characteristics(g); g = 5
for `side = :curve`, 4 for `:prym`) the signs in Igusa's formula
D(S) = c sum_m e_m theta^m (m over fundamental_completions(g, S)), c common to
all S of a sample, fixed by e = +1 at the first completion of `reference`.
Learned on the Jacobians of gs (gradient_samples): the signs of the reference
from the kernel of bracket_kernel_test with another set, then for each S by
least squares from D(S) / D(reference) P_reference(theta), rounded. Returns
(reference, table (S => (completions, signs)), worst (the largest relative
residual of a rounded sum)).
"""
function bracket_sign_table(gs, sets; side::Symbol = :curve, reference::Vector{Int} = first(sets),
                            verbose::Bool = true)
  LA = RSR.LinearAlgebra
  g = _side_genus(side)
  jac = [x for x in gs if x.type === :jacobian]
  @req length(jac) >= 2 * (g + 2) + 2 "Too few Jacobians to learn the signs."
  @req all(x -> hasproperty(x, :thetas), jac) "Recompute gs with the current gradient_samples (complex theta constants)."
  odds, evens = _odd_masks(g), _even_masks(g)
  R = sort(reference)
  other = first(S for S in sets if sort(S) != R)
  k = bracket_kernel_test(jac, [(R, sort(other))]; side = side, verbose = false)[1]
  v = k.coefficients[1:length(k.completions_S)]
  @req maximum(abs.(v .- round.(real.(v)))) < 1e-6 "The signs of the reference are not +-1."
  table = Dict{Vector{Int}, Tuple{Vector{Vector{Int}}, Vector{Int}}}(R => (k.completions_S, Int.(round.(real.(v)))))
  CR, eR = table[R]
  # D(reference) / P_reference per sample: the common factor c
  c = [LA.det(_side_gradients(x, side)[R, :]) / _igusa_sum(_side_thetas(x, side), CR, eR) for x in jac]
  worst = 0.0
  for S in sets
    S = sort(S)
    haskey(table, S) && continue
    C = _fundamental_completions(g, odds[S], evens)
    A = [prod(_side_thetas(x, side)[m]) for x in jac, m in C]
    r = [LA.det(_side_gradients(x, side)[S, :]) for x in jac] ./ c
    e = A \ r
    signs = Int.(round.(real.(e)))
    residual = LA.norm(A * signs - r) / LA.norm(r)
    @req all(s -> abs(s) == 1, signs) "Set $S: coefficients $(round.(e, digits = 3)) are not +-1."
    worst = max(worst, residual)
    table[S] = (C, signs)
  end
  verbose && println("$(length(table)) brackets, largest relative residual of the signed sums 10^",
                     round(log10(max(worst, 1e-300)), digits = 1))
  return (reference = R, table = table, worst = worst)
end

@doc raw"""
    theta_gradient_rows(theta_values, chain, signs, g) -> Matrix{ComplexF64}

The gradients of the odd theta functions at 0 (rows indexed by
odd_theta_characteristics(g)) from the theta constants `theta_values` (at
even_theta_characteristics(g)) alone, in the basis of the gradients of
chain.reference (those rows are the identity): Cramer's rule along
azygetic_basis_chain with the brackets from Igusa's formula (the signs of
bracket_sign_table). For gradients K (any basis) K = G K[reference, :].
"""
function theta_gradient_rows(theta_values::Vector{ComplexF64}, chain, signs, g::Int)
  table = signs isa Dict ? signs : signs.table
  n = length(odd_theta_characteristics(g))
  function bracket(S)
    C, e = table[sort(S)]
    return _permutation_sign(S) * _igusa_sum(theta_values, C, e)
  end
  G = zeros(ComplexF64, n, g)
  for (i, b) in enumerate(chain.reference)
    G[b, i] = 1
  end
  for x in chain.order
    B = chain.bases[x]
    DB = bracket(B)
    for j in eachindex(B)
      G[x, :] .+= (bracket([B[1:j-1]; x; B[j+1:end]]) / DB) .* G[B[j], :]
    end
  end
  return G
end

@doc raw"""
    gradient_formula_test(gs; side = :curve, seed = 1, learn = 20, formula = nothing,
                          verbose = true) -> NamedTuple

Learns the signs of the brackets (learn_gradient_formula) on the first
`learn` Jacobians of gs, or uses `formula` (load_gradient_formula), and
compares, for every sample, the gradients of the Fay
kernel with theta_gradient_rows (theta constants only):
max |K - G K[reference, :]| / max |K|. Prints one line per sample (type,
learned or not, log10 of the error).
"""
function gradient_formula_test(gs; side::Symbol = :curve, seed::Int = 1, learn::Int = 20, formula = nothing,
                               verbose::Bool = true)
  g = _side_genus(side)
  formula === nothing && (formula = learn_gradient_formula(gs; side = side, seed = seed, learn = learn, verbose = verbose))
  @req formula.genus == g "The formula is for genus $(formula.genus)."
  chain, signs = formula.chain, formula.signs
  learning = first([x for x in gs if x.type === :jacobian], learn)
  errors = Float64[]
  for (k, x) in enumerate(gs)
    K = _side_gradients(x, side)
    G = theta_gradient_rows(_side_thetas(x, side), chain, signs, g)
    err = maximum(abs, K - G * K[chain.reference, :]) / maximum(abs, K)
    push!(errors, err)
    verbose && println("sample $k: $(x.type)", any(y -> y === x, learning) ? " (learned)" : "",
                       ", error 10^", round(log10(max(err, 1e-300)), digits = 1))
  end
  return (genus = g, chain = chain, signs = signs, errors = errors)
end

################################################################################
#
#  The gradient formula as data, and the minors of M from theta constants
#
#  learn_gradient_formula fixes a chain and learns its signs; the result is
#  saved and loaded as a text file (save_gradient_formula), so the formula
#  does not depend on samples or on the random number generator.
#
#  theta_gradient_numerators clears the denominators per row: the rows of the
#  first round of the chain are G[x, :] = N[x, :] / D(reference) with
#  N[x, j] = D(reference with r_j replaced by x) (degree g + 2), the rows of the
#  second round have denominator D(reference) D(basis) and numerators of
#  degree 2(g + 2). The rank of M = [S | P] does not change when a row is
#  scaled, so row d of M times den(i1) den(i2) den_P(d)^2 is a row of
#  polynomials: [N_P[d]^2 den(i1) den(i2) | sym(N[i1], N[i2]) den_P(d)^2],
#  bihomogeneous in the theta constants of the curve and of the Prym. A
#  14 x 14 minor of that matrix is a polynomial in the theta constants that
#  vanishes on the Jacobians (rank 13), not on the intermediate Jacobians
#  (rank 15), for rows and columns chosen with choose_theta_minor.
#
#  lifted_reference_bases chooses the references so that 10 rows d of M are
#  cheap: d and both lifts in the first round (row degrees 2 * 6 resp.
#  2 * 7 instead of 2 * 12 resp. 2 * 14). More than 10 such rows do not exist
#  (checked by search), so a 14 x 14 minor has at least 4 rows from the
#  second round.
#
################################################################################

@doc raw"""
    lifted_reference_bases(; seed = 1) -> (curve, prym)

Reference bases for azygetic_basis_chain(5; reference = curve) and
azygetic_basis_chain(4; reference = prym): an azygetic set P of 5 odd
characteristics of genus 4, `curve` its lifts (0 a, 0 b) (indices into
odd_theta_characteristics(5)), `prym` its first 4 elements. The 10 odd d with
P + d azygetic have d in the first round of the Prym chain and both lifts in
the first round of the curve chain.
"""
function lifted_reference_bases(; seed::Int = 1)
  rng = Random.MersenneTwister(seed)
  odds4 = _odd_masks(4)
  n = length(odds4)
  az(i, j, k) = _azygetic_masks(odds4[i], odds4[j], odds4[k], 4)
  P = Int[]
  while length(P) < 5
    P = [rand(rng, 1:n)]
    for y in Random.shuffle(rng, collect(1:n))
      y in P && continue
      all(az(a, b, y) for (a, b) in _pairs_of(P)) || continue
      push!(P, y)
      length(P) == 5 && break
    end
  end
  lifts = RSR.lift_prym_indices(5)
  return sort([lifts[d][1] for d in P]), sort(P[1:4])
end

@doc raw"""
    learn_gradient_formula(gs; side = :curve, reference = nothing, seed = 1, learn = 20,
                           verbose = true) -> NamedTuple

The chain (azygetic_basis_chain, with the given reference basis if any) and
the signs of its brackets (bracket_sign_table, learned on the first `learn`
Jacobians of gs). Returns (genus, chain, signs); save it with
save_gradient_formula.
"""
function learn_gradient_formula(gs; side::Symbol = :curve, reference = nothing, seed::Int = 1,
                                learn::Int = 20, verbose::Bool = true)
  g = _side_genus(side)
  chain = azygetic_basis_chain(g; seed = seed, reference = reference)
  jac = first([x for x in gs if x.type === :jacobian], learn)
  signs = bracket_sign_table(jac, _chain_bracket_sets(chain); side = side, reference = chain.reference,
                             verbose = verbose)
  return (genus = g, chain = chain, signs = signs)
end

@doc raw"""
    save_gradient_formula(file, formula)

Writes a formula of learn_gradient_formula (or load_gradient_formula) as text:
`genus g`, `reference r_1 ... r_g`, one line `step x b_1 ... b_g` per row in
the order of the chain, and one line per bracket
`bracket s_1 ... s_g : e m_1 ... m_(g+2) : ...` (S sorted indices into
odd_theta_characteristics(g); per completion the sign e and the indices m
into even_theta_characteristics(g)).
"""
function save_gradient_formula(file::AbstractString, formula)
  chain, table = formula.chain, formula.signs.table
  open(file, "w") do io
    println(io, "genus ", formula.genus)
    println(io, "reference ", join(chain.reference, " "))
    for x in chain.order
      println(io, "step ", x, " ", join(chain.bases[x], " "))
    end
    for S in sort(collect(keys(table)))
      C, e = table[S]
      println(io, "bracket ", join(S, " "), " : ", join([string(s, " ", join(c, " ")) for (c, s) in zip(C, e)], " : "))
    end
  end
  return file
end

@doc raw"""
    load_gradient_formula(file) -> NamedTuple

Reads a file of save_gradient_formula; returns (genus, chain, signs) as
learn_gradient_formula.
"""
function load_gradient_formula(file::AbstractString)
  g = 0
  reference = Int[]
  order = Int[]
  bases = Dict{Int, Vector{Int}}()
  table = Dict{Vector{Int}, Tuple{Vector{Vector{Int}}, Vector{Int}}}()
  for line in eachline(file)
    words = split(line)
    isempty(words) && continue
    if words[1] == "genus"
      g = parse(Int, words[2])
    elseif words[1] == "reference"
      reference = parse.(Int, words[2:end])
    elseif words[1] == "step"
      x = parse(Int, words[2])
      push!(order, x)
      bases[x] = parse.(Int, words[3:end])
    elseif words[1] == "bracket"
      parts = split(line[length("bracket ")+1:end], ":")
      C = Vector{Int}[]
      e = Int[]
      for p in parts[2:end]
        v = parse.(Int, split(p))
        push!(e, v[1])
        push!(C, v[2:end])
      end
      table[parse.(Int, split(parts[1]))] = (C, e)
    end
  end
  @req g > 0 && length(reference) == g "Not a gradient formula file: $file"
  return (genus = g, chain = (reference = reference, order = order, bases = bases),
          signs = (reference = reference, table = table, worst = NaN))
end

@doc raw"""
    theta_gradient_numerators(theta_values, formula) -> NamedTuple

theta_gradient_rows with the denominators cleared per row: (numerators N,
denominators, degrees) with G[x, :] = N[x, :] / denominators[x]. Reference
rows: N = D(reference) e_j; first round: N[x, j] = D(reference with r_j
replaced by x), degree g + 2; second round: N[x, :] = sum_j D(B with b_j
replaced by x) N'[b_j, :] (N' over the denominator D(reference)), degree
2(g + 2), denominator D(reference) D(B). The D are Igusa's sums of the
formula.
"""
function theta_gradient_numerators(theta_values::AbstractVector, formula)
  g, chain, table = formula.genus, formula.chain, formula.signs.table
  n = length(odd_theta_characteristics(g))
  function bracket(S)
    C, e = table[sort(S)]
    return _permutation_sign(S) * _igusa_sum(theta_values, C, e)
  end
  R = chain.reference
  DR = bracket(R)
  # (the entries are replaced, never changed in place: fill is safe for balls)
  N = fill(zero(theta_values[1]), n, g)
  denominators = fill(zero(theta_values[1]), n)
  degrees = fill(-1, n)
  round = zeros(Int, n)
  for (i, b) in enumerate(R)
    N[b, i] = DR
    denominators[b] = DR
    degrees[b] = g + 2
  end
  for x in chain.order
    B = chain.bases[x]
    if B == R
      for j in 1:g
        N[x, j] = bracket([R[1:j-1]; x; R[j+1:end]])
      end
      denominators[x] = DR
      degrees[x] = g + 2
      round[x] = 1
    else
      @req all(b -> round[b] <= 1 && degrees[b] >= 0, B) "Row $x: its basis is not in the first round."
      for j in eachindex(B)
        c = bracket([B[1:j-1]; x; B[j+1:end]])
        for k in 1:g
          N[x, k] = N[x, k] + c * N[B[j], k]
        end
      end
      denominators[x] = DR * bracket(B)
      degrees[x] = 2 * (g + 2)
      round[x] = 2
    end
  end
  return (numerators = N, denominators = denominators, degrees = degrees, round = round)
end

# Row d of M (gradient_rank_matrix) from the numerators, times
# den(i1) den(i2) den_P(d)^2.
function _theta_M_row(curve, prym, d::Int, lifts)
  i1, i2 = lifts[d]
  Np, Dp = prym.numerators, prym.denominators
  N, D = curve.numerators, curve.denominators
  S = [Np[d, x] * Np[d, y] * D[i1] * D[i2] for (x, y) in _lower_monomials(4)]
  P = [(N[i1, x] * N[i2, y] + N[i2, x] * N[i1, y]) * Dp[d]^2 for (x, y) in _lower_monomials(5)]
  return [S; P]
end

@doc raw"""
    theta_M(x, curve, prym; rows = 1:120) -> Matrix{ComplexF64}

For a sample x (gradient_samples) and the formulas `curve` (genus 5) and
`prym` (genus 4) (load_gradient_formula): the rows `rows` (indices into
odd_theta_characteristics(4)) of M = [S | P] of gradient_rank_matrix, from the
theta constants only, in the bases of the gradients of the reference rows,
row d multiplied by den(i1) den(i2) den_P(d)^2: polynomial entries
[N_P[d]^2 den(i1) den(i2) | sym(N[i1], N[i2]) den_P(d)^2].
"""
function theta_M(x, curve, prym; rows = 1:120)
  c = theta_gradient_numerators(x.thetas, curve)
  p = theta_gradient_numerators(x.thetas_prym, prym)
  lifts = RSR.lift_prym_indices(5)
  return reduce(vcat, [transpose(_theta_M_row(c, p, d, lifts)) for d in rows])
end

@doc raw"""
    theta_M_degrees(curve, prym, rows) -> Vector{Tuple{Int, Int}}

The bidegrees (curve theta constants, Prym theta constants) of the rows of
theta_M: row d is homogeneous of degree deg N[i1] + deg N[i2] in the theta
constants of the curve and 2 deg N_P[d] in those of the Prym.
"""
function theta_M_degrees(curve, prym, rows)
  c = theta_gradient_numerators(ones(ComplexF64, length(even_theta_characteristics(5))), curve).degrees
  p = theta_gradient_numerators(ones(ComplexF64, length(even_theta_characteristics(4))), prym).degrees
  lifts = RSR.lift_prym_indices(5)
  return [(c[lifts[d][1]] + c[lifts[d][2]], 2 * p[d]) for d in rows]
end

# log10 of |det| / prod of the row norms (Hadamard: <= 0)
function _normalized_log10_det(A::Matrix{ComplexF64})
  LA = RSR.LinearAlgebra
  B = A ./ [LA.norm(A[i, :]) for i in 1:size(A, 1)]
  return log10(max(abs(LA.det(B)), 1e-300))
end

@doc raw"""
    choose_theta_minor(gs, curve, prym; size = 14, verbose = true) -> NamedTuple

Rows and columns of a size x size minor of theta_M that does not vanish on
the intermediate Jacobians of gs: rows greedily (cheapest bidegree first) as
long as the rank on the first intermediate Jacobian grows, then all 10
Prym columns and greedily columns of P. Prints the bidegree of the minor.
"""
function choose_theta_minor(gs, curve, prym; size::Int = 14, verbose::Bool = true)
  LA = RSR.LinearAlgebra
  ij = [x for x in gs if x.type !== :jacobian]
  @req !isempty(ij) "Needs an intermediate Jacobian among the samples."
  M = theta_M(ij[1], curve, prym)
  M = M ./ [LA.norm(M[i, :]) for i in 1:Base.size(M, 1)]
  degrees = theta_M_degrees(curve, prym, 1:Base.size(M, 1))
  candidates = sortperm(degrees; by = d -> d[1] + d[2])
  rank_of(A) = (s = LA.svdvals(A); count(>(1e-8 * s[1]), s))
  rows = Int[]
  for d in candidates
    rank_of(M[[rows; d], :]) > length(rows) && push!(rows, d)
    length(rows) == size && break
  end
  @req length(rows) == size "M has rank $(length(rows)) < $size on the intermediate Jacobian."
  columns = collect(1:10)
  rank_of(M[rows, columns]) == 10 || (columns = Int[])
  for c in 1:25
    c in columns && continue
    rank_of(M[rows, [columns; c]]) > length(columns) && push!(columns, c)
    length(columns) == size && break
  end
  sort!(rows)
  sort!(columns)
  bidegree = (sum(first, degrees[rows]), sum(last, degrees[rows]))
  verbose && println("rows $rows, columns $columns, bidegree $bidegree (curve, Prym theta constants)")
  return (rows = rows, columns = columns, bidegree = bidegree)
end

@doc raw"""
    theta_minor_test(gs, curve, prym, minor; verbose = true) -> Vector{Float64}

log10 of the normalized minor (|det| over the product of the row norms) of
theta_M at the rows and columns of `minor` (choose_theta_minor) on every
sample of gs; also the same minor of the matrix M of the Fay gradients in the
same bases (K K[reference, :]^-1), which must agree up to the row scaling.
Prints one line per sample.
"""
function theta_minor_test(gs, curve, prym, minor; verbose::Bool = true)
  LA = RSR.LinearAlgebra
  lifts = RSR.lift_prym_indices(5)
  values = Float64[]
  for (k, x) in enumerate(gs)
    A = theta_M(x, curve, prym; rows = minor.rows)[:, minor.columns]
    v = _normalized_log10_det(A)
    # the same minor from the Fay gradients in the reference bases
    K = x.K / x.K[curve.chain.reference, :]
    Kp = x.K_prym / x.K_prym[prym.chain.reference, :]
    F = reduce(vcat, [transpose([[Kp[d, a] * Kp[d, b] for (a, b) in _lower_monomials(4)];
                                 [K[lifts[d][1], a] * K[lifts[d][2], b] + K[lifts[d][2], a] * K[lifts[d][1], b]
                                  for (a, b) in _lower_monomials(5)]]) for d in minor.rows])[:, minor.columns]
    w = _normalized_log10_det(F)
    push!(values, v)
    verbose && println("sample $k: $(x.type), minor 10^$(round(v, digits = 1)) (Fay gradients 10^$(round(w, digits = 1)))")
  end
  return values
end

@doc raw"""
    theta_minor_values(samples, curve, prym, minor; sign_data = nothing, verbose = true)
      -> Vector{NamedTuple}

The minor of choose_theta_minor at full precision (balls) for samples of
load_theta_data (the theta constants of the curve; the Prym by Schottky-Jung
with the signs of correct_signs_with_data!, as in gradient_rank_matrix):
log2 |minor| relative to the product of the largest entries of its rows, and
whether the ball contains 0 (then the value is the log2 of its radius, an
upper bound). On a Jacobian it should be about minus the precision of the
theta constants, on an intermediate Jacobian of moderate size.
"""
function theta_minor_values(samples, curve, prym, minor; sign_data = nothing, verbose::Bool = true)
  data4 = _loaded_sign_data(sign_data, 4)
  evens5 = [Tuple(c) for c in even_theta_characteristics(5)]
  evens4 = [Tuple(c) for c in even_theta_characteristics(4)]
  out = NamedTuple[]
  for (k, s) in enumerate(samples)
    th = Dict{NTuple{10, Int}, AcbFieldElem}(Tuple(c) => v for (c, v) in s[:thetas])
    CC = parent(first(values(th)))
    for c in odd_theta_characteristics(5)
      haskey(th, Tuple(c)) || (th[Tuple(c)] = zero(CC))
    end
    thetas_prym = prym_thetas(5, th)
    correct_signs_with_data!(thetas_prym, 4, data4; fallback = true)
    x = (thetas = [th[e] for e in evens5], thetas_prym = [thetas_prym[e] for e in evens4])
    A = theta_M(x, curve, prym; rows = minor.rows)[:, minor.columns]
    scale = sum(maximum(RSR._log2_abs(a) for a in A[i, :]) for i in 1:size(A, 1))
    D = det(matrix(CC, A))
    zero_ball = contains_zero(D)
    value = (zero_ball ? RSR._log2_radius(D) : RSR._log2_abs(D)) - scale
    push!(out, (type = s[:type], log2_minor = value, contains_zero = zero_ball, bits = get(s, :bits, missing)))
    verbose && println("sample $k: $(s[:type]), minor ", zero_ball ? "<= " : "", "2^", round(value, digits = 1),
                       " (theta constants to $(get(s, :bits, "?")) bits)")
  end
  return out
end

################################################################################
#
#  The normal space of the Jacobian locus from the minors
#
#  The minors of theta_M vanish on the Jacobian locus J_5 (codimension 3 in
#  A_5). At a Jacobian tau the differentials of the minors with respect to
#  the 15 coordinates of tau span at most the normal space; if they span a
#  space of dimension 3, the minors cut out J_5 near tau as a reduced scheme
#  (and a few of them suffice). minor_normal_space computes the differentials
#  with residual_jacobian (heat equation) and their rank; with `compare` (for
#  example accola_system(product = true)) it also checks that the
#  differentials of another system vanishing on J_5 lie in the same space.
#
################################################################################

@doc raw"""
    random_theta_minors(count; seed = 1, size = 14) -> Vector{NamedTuple}

`count` random minors of theta_M: `size` random rows (of 120) and all 10 Prym
columns with `size - 10` random columns of P.
"""
function random_theta_minors(count::Int; seed::Int = 1, size::Int = 14)
  rng = Random.MersenneTwister(seed)
  return [(rows = sort(Random.randperm(rng, 120)[1:size]),
           columns = sort([collect(1:10); 10 .+ Random.randperm(rng, 15)[1:size-10]])) for _ in 1:count]
end

@doc raw"""
    theta_minor_system(curve, prym, minors; sign_data = nothing) -> ThetaEquationSystem

The minors (NamedTuples with rows and columns: choose_theta_minor,
random_theta_minors) of theta_M as a system of equations in the theta
constants, for residual_jacobian and project_to_locus. The state, set at the
first evaluation, holds the Prym theta constants (Schottky-Jung with the
signs of correct_signs_with_data!), whose branches are then followed (the
square root nearest to them), and per minor the power of 2 that scales it
(the product of the largest entries of its rows).
"""
function theta_minor_system(curve, prym, minors; sign_data = nothing)
  data4 = _loaded_sign_data(sign_data, 4)
  evens5 = [Tuple(c) for c in even_theta_characteristics(5)]
  evens4 = [Tuple(c) for c in even_theta_characteristics(4)]
  rows = sort(unique(reduce(vcat, [m.rows for m in minors])))
  position = Dict(d => i for (i, d) in enumerate(rows))
  function residual(g, thetas, state)
    th = Dict{NTuple{10, Int}, AcbFieldElem}(Tuple(c) => v for (c, v) in thetas)
    CC = parent(first(values(th)))
    for c in odd_theta_characteristics(5)
      haskey(th, Tuple(c)) || (th[Tuple(c)] = zero(CC))
    end
    if state === nothing
      tp = prym_thetas(5, th)
      correct_signs_with_data!(tp, 4, data4; fallback = true)
      prym_values = [tp[e] for e in evens4]
    else
      squares = prym_thetas_sq(5, th)
      prym_values = map(evens4, state.prym) do e, base
        r = sqrt(squares[e])
        RSR._abs64(r - base) <= RSR._abs64(r + base) ? r : -r
      end
    end
    x = (thetas = [th[e] for e in evens5], thetas_prym = prym_values)
    A = theta_M(x, curve, prym; rows = rows)
    blocks = [A[[position[d] for d in m.rows], m.columns] for m in minors]
    exponents = state === nothing ?
                [round(Int, sum(maximum(RSR._log2_abs(b[i, j]) for j in 1:size(b, 2)) for i in 1:size(b, 1)))
                 for b in blocks] : state.exponents
    minor_values = map(blocks, exponents) do b, e
      v = det(matrix(CC, b))
      _scale_2exp!(v, e)   # (in place; returns nothing)
      return v
    end
    return minor_values, (prym = prym_values, exponents = exponents)
  end
  return ThetaEquationSystem("theta minors", residual, ZZMatrix[])
end

@doc raw"""
    minor_normal_space(tau, curve, prym, minors; prec = 256, step = 2.0^-60, method = :heat,
                       compare = nothing, sign_data = nothing, verbose = true) -> NamedTuple

At tau (a period matrix of a curve of genus 5, known to more than `prec`
bits): the values of the minors (theta_minor_system, scaled; about
2^-prec on J_5), the Jacobian of the minors with respect to the 15
coordinates of tau (residual_jacobian), its singular values (log2, relative
to the largest) and numerical rank (3 if the minors cut out J_5 near tau
as a reduced scheme). With `compare` (a ThetaEquationSystem vanishing on
J_5, e.g. accola_system(product = true)) also the relative distance of the
rows of its Jacobian to the row space of the first `rank` singular vectors
(about 2^-prec/2 if they lie in the same normal space).
"""
function minor_normal_space(tau::AcbMatrix, curve, prym, minors; prec::Int = 256, step::Float64 = 2.0^-60,
                            method::Symbol = :heat, compare = nothing, sign_data = nothing, verbose::Bool = true)
  LA = RSR.LinearAlgebra
  S = theta_minor_system(curve, prym, minors; sign_data = sign_data)
  t = _change_precision(tau, AcbField(prec))
  clock = time()
  minor_values, states = _system_residual(S, t)
  values_log2 = [RSR._log2_abs(v) for v in minor_values]
  J = residual_jacobian(S, tau, states; prec = prec, step = step, method = method)
  F = LA.svd(J)
  singular_log2 = [RSR._safe_log2(s / F.S[1]) for s in F.S]
  rank = _numerical_rank(F.S)
  verbose && println("$(length(minors)) minors: values 2^", round(maximum(values_log2), digits = 1), " (largest), ",
                     "Jacobian rank $rank, singular values 2^", round.(singular_log2, digits = 1), ", ",
                     round(time() - clock, digits = 1), " s")
  distance = nothing
  if compare !== nothing
    _, states_compare = _system_residual(compare, t)
    A = residual_jacobian(compare, tau, states_compare; prec = prec, step = step, method = method)
    V = F.V[:, 1:rank]
    distance = RSR._safe_log2(LA.norm(A - A * V * V') / LA.norm(A))
    verbose && println("    $(compare.name): rows of its Jacobian off the normal space 2^", round(distance, digits = 1),
                       " (relative; rank of its Jacobian ", _numerical_rank(LA.svdvals(A)), ")")
  end
  return (values_log2 = values_log2, jacobian = J, singular_values_log2 = singular_log2, rank = rank,
          compare_distance_log2 = distance)
end

################################################################################
#
#  M in brackets: no chain, no denominators
#
#  The rank of M = [S | P] does not change under a change of coordinates of
#  the columns. Instead of coordinates in a basis of gradients use the
#  linear forms l_T(v) = det(grad theta[T], v), T a set of g - 1 odd
#  characteristics: l_T(grad theta[x]) = D(T + x), Igusa's sum if T + x is
#  azygetic. For an azygetic set T' = {t_1, ..., t_4} of odd characteristics
#  of genus 4 there are exactly 20 odd d with T' + d azygetic, and for every
#  lift T of T' (t_i -> (0 t_i', e_i 0 t_i''), 16 choices) both T + d~ and
#  T + d~ + eta are azygetic (d~, d~ + eta the lifts of d). So, with T_1, ...,
#  T_5 five lifts (their forms independent) and the dual forms
#  l_(T' - t_a) on the Prym side, the 20 x 25 matrix
#
#    Mb[d, ab] = D_P(T' - t_a + d) D_P(T' - t_b + d)                (a <= b <= 4)
#    Mb[d, kl] = D(T_k + d~) D(T_l + d~ + eta) + D(T_k + d~ + eta) D(T_l + d~)
#                                                                  (k <= l <= 5)
#
#  is M[rows, :] times an invertible block diagonal matrix (and the constants
#  of Igusa's formula): the same rank. Its entries are sums over pairs of
#  fundamental systems of products of 12 Prym (resp. 14 curve) theta
#  constants; a 14 x 14 minor with 10 Prym and 4 curve columns has bidegree
#  (56, 120).
#
################################################################################

@doc raw"""
    bracket_M_setup(; seed = 1, lift_bits = nothing) -> NamedTuple

A random (seeded) azygetic set T' of 4 odd characteristics of genus 4
(`prym_reference`, indices into odd_theta_characteristics(4)), the 20 rows d
(T' + d azygetic), the Prym column sets T' - t_a and five lifts T_k of T'
(indices into odd_theta_characteristics(5); `lift_bits[k][i]` is the b_1 of
the lift of t_i, default 0000, 1000, 0100, 0010, 0001).
"""
function bracket_M_setup(; seed::Int = 1, lift_bits = nothing)
  rng = Random.MersenneTwister(seed)
  odds = _odd_masks(4)
  n = length(odds)
  az(i, j, k) = _azygetic_masks(odds[i], odds[j], odds[k], 4)
  T = Int[]
  while length(T) < 4
    T = [rand(rng, 1:n)]
    for y in Random.shuffle(rng, collect(1:n))
      y in T && continue
      all(az(a, b, y) for (a, b) in _pairs_of(T)) || continue
      push!(T, y)
      length(T) == 4 && break
    end
  end
  sort!(T)
  rows = [d for d in 1:n if !(d in T) && all(az(a, b, d) for (a, b) in _pairs_of(T))]
  lift_bits === nothing && (lift_bits = [[0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
  lifts = RSR.lift_prym_indices(5)
  curve_sets = [[lifts[t][e + 1] for (t, e) in zip(T, bits)] for bits in lift_bits]
  prym_sets = [T[[1:a-1; a+1:4]] for a in 1:4]
  return (prym_reference = T, rows = rows, prym_sets = prym_sets, curve_sets = curve_sets, lifts = lifts)
end

# The sorted sets whose brackets bracket_M needs (curve, Prym).
function _bracket_M_sets(setup)
  curve = Set{Vector{Int}}()
  prym = Set{Vector{Int}}()
  for d in setup.rows
    for T in setup.curve_sets, i in setup.lifts[d]
      push!(curve, sort([T; i]))
    end
    for T in setup.prym_sets
      push!(prym, sort([T; d]))
    end
  end
  return sort(collect(curve)), sort(collect(prym))
end

@doc raw"""
    learn_bracket_M_signs(gs, setup; learn = 20, verbose = true) -> NamedTuple

The signs of Igusa's sums for the brackets of bracket_M (bracket_sign_table
on the first `learn` Jacobians of gs): (curve, prym) tables.
"""
function learn_bracket_M_signs(gs, setup; learn::Int = 20, verbose::Bool = true)
  jac = first([x for x in gs if x.type === :jacobian], learn)
  curve_sets, prym_sets = _bracket_M_sets(setup)
  curve = bracket_sign_table(jac, curve_sets; side = :curve, verbose = verbose).table
  prym = bracket_sign_table(jac, prym_sets; side = :prym, verbose = verbose).table
  return (curve = curve, prym = prym)
end

# The bracket of the ordered set S: Igusa's sum (table) or, with K, det K[S, :].
function _ordered_bracket(S, theta_values, table)
  C, e = table[sort(S)]
  return _permutation_sign(S) * _igusa_sum(theta_values, C, e)
end

# Mb from a bracket function of (side, ordered set).
function _bracket_M_from(bracket, setup)
  rows = Vector{Any}[]
  for d in setup.rows
    i1, i2 = setup.lifts[d]
    lp = [bracket(:prym, [T; d]) for T in setup.prym_sets]
    l1 = [bracket(:curve, [T; i1]) for T in setup.curve_sets]
    l2 = [bracket(:curve, [T; i2]) for T in setup.curve_sets]
    push!(rows, [[lp[a] * lp[b] for (a, b) in _lower_monomials(4)];
                 [l1[k] * l2[l] + l2[k] * l1[l] for (k, l) in _lower_monomials(5)]])
  end
  return permutedims(reduce(hcat, rows))
end

@doc raw"""
    bracket_M(x, setup, signs) -> Matrix

The 20 x 25 matrix Mb (see above) for a sample x with theta constants of the
curve and of the Prym (x.thetas, x.thetas_prym at even_theta_characteristics;
ComplexF64 or balls), from Igusa's sums with the signs of
learn_bracket_M_signs. Rows: setup.rows; columns: the 10 Prym products, then
the 15 curve products (as in gradient_rank_matrix).
"""
function bracket_M(x, setup, signs)
  bracket(side, S) = side === :curve ? _ordered_bracket(S, x.thetas, signs.curve) :
                                       _ordered_bracket(S, x.thetas_prym, signs.prym)
  M = _bracket_M_from(bracket, setup)
  return [M[i, j] for i in 1:size(M, 1), j in 1:size(M, 2)]
end

@doc raw"""
    bracket_M_test(gs, setup, signs; verbose = true) -> Vector{NamedTuple}

For every sample of gs (gradient_samples): Mb from the theta constants
against the same matrix from the brackets det K[S, :] of the Fay gradients
(they agree up to a factor per column block: the constants of Igusa's
formula); the rank of the five curve forms l_(T_k) (must be 5); and the
singular values 11 to 17 of Mb (log10, relative), Float64.
"""
function bracket_M_test(gs, setup, signs; verbose::Bool = true)
  LA = RSR.LinearAlgebra
  out = NamedTuple[]
  for (k, x) in enumerate(gs)
    A = ComplexF64.(bracket_M(x, setup, signs))
    fay(side, S) = LA.det((side === :curve ? x.K : x.K_prym)[S, :])
    B = ComplexF64.(_bracket_M_from(fay, setup))
    deviation = 0.0
    for block in (1:10, 11:25)
      r = sum(B[:, block] .* conj.(A[:, block])) / sum(abs2, A[:, block])
      deviation = max(deviation, LA.norm(B[:, block] - r * A[:, block]) / LA.norm(B[:, block]))
    end
    # the forms l_T as vectors: l_T(e_j) = det([K[T, :]; e_j])
    forms = [LA.det([x.K[T, :]; transpose([i == j ? 1.0 + 0im : 0.0im for i in 1:5])]) for T in setup.curve_sets, j in 1:5]
    s_forms = LA.svdvals(forms)
    form_rank = count(>(1e-8 * s_forms[1]), s_forms)
    An = A ./ [LA.norm(A[i, :]) for i in 1:size(A, 1)]
    An = An ./ transpose([LA.norm(An[:, j]) for j in 1:size(An, 2)])
    s = LA.svdvals(An)
    sv = round.(log10.(max.(s[11:min(17, end)] ./ s[1], 1e-300)), digits = 1)
    push!(out, (type = x.type, deviation = deviation, form_rank = form_rank, singular_values_log10 = sv))
    verbose && println("sample $k: $(x.type), against Fay 10^$(round(log10(max(deviation, 1e-300)), digits = 1)), ",
                       "forms of rank $form_rank, singular values 11-17: 10^$sv")
  end
  return out
end

@doc raw"""
    choose_bracket_minor(gs, setup, signs; size = 14, verbose = true) -> NamedTuple

Rows (positions in setup.rows) and columns of a size x size minor of
bracket_M that is as far from vanishing as possible on the intermediate
Jacobians of gs (rows and columns normalized): greedily the row, then (after
the 10 Prym columns) the column that maximizes the smallest over the
intermediate Jacobians of the smallest singular value. Prints that value
(log10) and the bidegree of the minor.
"""
function choose_bracket_minor(gs, setup, signs; size::Int = 14, verbose::Bool = true)
  LA = RSR.LinearAlgebra
  ij = [x for x in gs if x.type !== :jacobian]
  @req !isempty(ij) "Needs an intermediate Jacobian among the samples."
  function normalized(x)
    M = ComplexF64.(bracket_M(x, setup, signs))
    M = M ./ [LA.norm(M[i, :]) for i in 1:Base.size(M, 1)]
    return M ./ transpose([LA.norm(M[:, j]) for j in 1:Base.size(M, 2)])
  end
  Ms = [normalized(x) for x in ij]
  # the smallest singular value of the submatrix, minimized over the samples
  score(rows, columns) = minimum(minimum(LA.svdvals(M[rows, columns])) for M in Ms)
  n_rows, n_columns = Base.size(Ms[1])
  rows = Int[]
  while length(rows) < size
    candidates = [d for d in 1:n_rows if !(d in rows)]
    push!(rows, candidates[argmax([score([rows; d], 1:n_columns) for d in candidates])])
  end
  columns = collect(1:min(10, size))
  while length(columns) < size
    candidates = [c for c in 1:n_columns if !(c in columns)]
    push!(columns, candidates[argmax([score(rows, [columns; c]) for c in candidates])])
  end
  sort!(rows)
  sort!(columns)
  value = score(rows, columns)
  verbose && println("rows $rows (characteristics $(setup.rows[rows])), columns $columns, smallest singular value ",
                     "on the intermediate Jacobians 10^", round(log10(max(value, 1e-300)), digits = 1), ", bidegree ",
                     (14 * count(>(10), columns), 12 * count(<=(10), columns)), " (curve, Prym theta constants)")
  return (rows = rows, columns = columns)
end

# The theta constants of a sample of load_theta_data as vectors at
# even_theta_characteristics(5) and (Prym, Schottky-Jung with corrected
# signs) at even_theta_characteristics(4).
function _sample_theta_vectors(s, data4)
  th = Dict{NTuple{10, Int}, AcbFieldElem}(Tuple(c) => v for (c, v) in s[:thetas])
  CC = parent(first(values(th)))
  for c in odd_theta_characteristics(5)
    haskey(th, Tuple(c)) || (th[Tuple(c)] = zero(CC))
  end
  thetas_prym = prym_thetas(5, th)
  correct_signs_with_data!(thetas_prym, 4, data4; fallback = true)
  return (thetas = [th[Tuple(e)] for e in even_theta_characteristics(5)],
          thetas_prym = [thetas_prym[Tuple(e)] for e in even_theta_characteristics(4)])
end

@doc raw"""
    bracket_minor_values(samples, setup, signs, minor; sign_data = nothing, verbose = true)
      -> Vector{NamedTuple}

The minor of choose_bracket_minor at full precision (balls) for samples of
load_theta_data, as theta_minor_values: log2 |minor| relative to the
product of the largest entries of its rows (an upper bound from the radius
when the ball contains 0).
"""
function bracket_minor_values(samples, setup, signs, minor; sign_data = nothing, verbose::Bool = true)
  data4 = _loaded_sign_data(sign_data, 4)
  out = NamedTuple[]
  for (k, s) in enumerate(samples)
    x = _sample_theta_vectors(s, data4)
    A = bracket_M(x, setup, signs)[minor.rows, minor.columns]
    @req size(A, 1) == size(A, 2) "The minor is not square: $(size(A))."
    CC = parent(A[1, 1])
    scale = sum(maximum(RSR._log2_abs(a) for a in A[i, :]) for i in 1:size(A, 1))
    D = det(matrix(CC, A))
    zero_ball = contains_zero(D)
    value = (zero_ball ? RSR._log2_radius(D) : RSR._log2_abs(D)) - scale
    push!(out, (type = s[:type], log2_minor = value, contains_zero = zero_ball, bits = get(s, :bits, missing)))
    verbose && println("sample $k: $(s[:type]), minor ", zero_ball ? "<= " : "", "2^", round(value, digits = 1),
                       " (theta constants to $(get(s, :bits, "?")) bits)")
  end
  return out
end

################################################################################
#
#  The signs in Igusa's formula from the theta transformation formula
#
#  Sp(2g, Z/2) acts simply transitively on the ordered fundamental systems
#  (n_1, ..., n_g odd, m_1, ..., m_(g+2) even), and every bijection between
#  two of them is realized. Fix a base system F0 = (S0, C0) and normalize
#  Igusa's formula by sign +1 on the monomial C0 of D(S0). For an azygetic
#  set S (sorted) and a completion C let M in Sp(2g, Z) map F0 to (S, C)
#  (mod 2, ordered; M is a product of integral transvections
#  T_v = 1 + v v^t J, J = [0 1; -1 0]). Igusa's transformation formula
#
#    theta[M.m](M tau) = kappa(M) e(phi_m(M)) det(C tau + D)^(1/2) theta[m](tau),
#    M.m = [D -C; -B A] m + (diag(C D^t), diag(A B^t)),
#    phi_m(M) = -(m'^t B^t D m' + m''^t A^t C m'' - 2 m'^t B^t C m'') / 8
#               + (D m' - C m'')^t diag(A B^t) / 4,
#
#  applied to the g gradients and the g + 2 theta constants gives
#
#    eps(S, C) = kappa(M)^-2 e(sum_(n in S0) phi_n(M) - sum_(m in C0) phi_m(M))
#                * prod over the 2g + 2 images of (-1)^(r' . l'')
#
#  (the image M.m = r + 2l with r in {0, 1}^2g: theta[r + 2l] =
#  (-1)^(r' . l'') theta[r]; the powers of det(C tau + D) cancel). kappa(M)^2
#  is multiplicative along the transvections up to the phases of the
#  intermediate characteristics: kappa(M1 M2)^2 = kappa(M1)^2 kappa(M2)^2
#  e(2 (phi_(M2.0)(M1) + phi_0(M2) - phi_0(M1 M2))), and
#  kappa(T_v)^2 = i if k = v' . v'' is odd, (-1)^(k/2) if k is even
#  (checked numerically for g <= 5). The result reproduces all learned sign
#  tables (genus 3, 4, 5; 368, 600, 500 sets, random tau).
#
#  Phases are kept exactly as exponents of zeta_8 = e(1/8).
#
################################################################################

_f2(x) = mod.(x, 2)

function _f2_inverse(A::Matrix{Int})
  n = size(A, 1)
  M = hcat(_f2(A), Matrix{Int}(RSR.LinearAlgebra.I, n, n))
  r = 1
  for c in 1:n
    p = findfirst(i -> M[i, c] == 1, r:n)
    @req p !== nothing "Singular matrix over GF(2)."
    p += r - 1
    M[[r, p], :] = M[[p, r], :]
    for i in 1:n
      i != r && M[i, c] == 1 && (M[i, :] = _f2(M[i, :] .+ M[r, :]))
    end
    r += 1
  end
  return M[:, n+1:end]
end

# the symplectic form mod 2 and the transvection x -> x + w(x, v) v
_f2_form(x, y, g::Int) = mod(sum(x[i] * y[g+i] + x[g+i] * y[i] for i in 1:g), 2)
_f2_transvect(v, x, g::Int) = _f2(x .+ _f2_form(x, v, g) .* v)

# vectors v_1, ..., v_k with N = T_(v_1) ... T_(v_k) over GF(2) (N symplectic)
function _transvection_word(N::Matrix{Int}, g::Int)
  n = 2 * g
  unit(i) = [j == i ? 1 : 0 for j in 1:n]
  word = Vector{Vector{Int}}()
  current = copy(N)
  function apply!(v)
    push!(word, v)
    for c in 1:n
      current[:, c] = _f2_transvect(v, current[:, c], g)
    end
  end
  fixed = Int[]
  function send!(x, y)
    x == y && return
    if _f2_form(x, y, g) == 1
      apply!(_f2(x .+ y))
      return
    end
    free = [i for i in 1:g if !(i in fixed)]
    for bits in 1:(4^length(free) - 1)
      z = zeros(Int, n)
      b = bits
      for i in free
        isodd(b) && (z[i] = 1)
        b >>= 1
        isodd(b) && (z[g + i] = 1)
        b >>= 1
      end
      if _f2_form(x, z, g) == 1 && _f2_form(y, z, g) == 1
        apply!(_f2(x .+ z))
        apply!(_f2(z .+ y))
        return
      end
    end
    error("No transvection path (not symplectic?).")
  end
  for i in 1:g
    send!(current[:, i], unit(i))
    x, y = current[:, g + i], unit(g + i)
    if x != y
      if _f2_form(x, y, g) == 1
        apply!(_f2(x .+ y))
      else
        z = _f2(unit(i) .+ y)
        apply!(_f2(x .+ z))
        apply!(_f2(z .+ y))
      end
    end
    push!(fixed, i)
  end
  @assert current == Matrix{Int}(RSR.LinearAlgebra.I, n, n)
  return word
end

function _integral_transvection(v::Vector{Int}, g::Int)
  J = [zeros(Int, g, g) Matrix{Int}(RSR.LinearAlgebra.I, g, g); -Matrix{Int}(RSR.LinearAlgebra.I, g, g) zeros(Int, g, g)]
  return Matrix{Int}(RSR.LinearAlgebra.I, 2 * g, 2 * g) + v * transpose(v) * J
end

# M.m (integral) and 8 phi_m(M) (an integer)
function _igusa_action(M::Matrix{Int}, m::Vector{Int}, g::Int)
  A, B, C, D = M[1:g, 1:g], M[1:g, g+1:end], M[g+1:end, 1:g], M[g+1:end, g+1:end]
  a, b = m[1:g], m[g+1:end]
  dCD = [sum(C[i, :] .* D[i, :]) for i in 1:g]
  dAB = [sum(A[i, :] .* B[i, :]) for i in 1:g]
  image = [D * a - C * b + dCD; -B * a + A * b + dAB]
  phi8 = -(a' * B' * D * a + b' * A' * C * b - 2 * a' * B' * C * b) + 2 * ((D * a - C * b)' * dAB)
  return image, phi8
end

# (-1)^(r' . l'') for m = r + 2l
function _reduction_sign(m::Vector{Int}, g::Int)
  r = _f2(m)
  l = (m[g+1:end] .- r[g+1:end]) .÷ 2
  return iseven(sum(r[1:g] .* l)) ? 1 : -1
end

# kappa(M)^2 as an exponent of zeta_8, for M = T_(v_1) ... T_(v_k)
function _kappa2_exponent(word::Vector{Vector{Int}}, g::Int)
  Ts = [_integral_transvection(v, g) for v in word]
  M = reduce(*, Ts; init = Matrix{Int}(RSR.LinearAlgebra.I, 2 * g, 2 * g))
  m = zeros(Int, 2 * g)
  total8 = 0
  exponent = 0
  for i in length(Ts):-1:1
    m, phi8 = _igusa_action(Ts[i], m, g)
    total8 += phi8
    k = sum(word[i][1:g] .* word[i][g+1:end])
    exponent += isodd(k) ? 2 : (iseven(k ÷ 2) ? 0 : 4)
  end
  _, phiM8 = _igusa_action(M, zeros(Int, 2 * g), g)
  return mod(exponent + 2 * (total8 - phiM8), 8), M
end

# the base fundamental system: the lexicographically first azygetic g-set of
# odd characteristics and its first completion
function _igusa_base(g::Int)
  odds, evens = _odd_masks(g), _even_masks(g)
  az(i, j, k) = _azygetic_masks(odds[i], odds[j], odds[k], g)
  S = Int[]
  function extend(start)
    length(S) == g && return true
    for y in start:length(odds)
      all(az(a, b, y) for (a, b) in _pairs_of(S)) || continue
      push!(S, y)
      extend(y + 1) && return true
      pop!(S)
    end
    return false
  end
  extend(1)
  return S, first(_fundamental_completions(g, odds[S], evens))
end

@doc raw"""
    igusa_sign(g, S, C) -> Int

The sign of the monomial theta[C] in Igusa's formula for the bracket D(S)
(S sorted indices into odd_theta_characteristics(g), an azygetic set; C a
completion, indices into even_theta_characteristics(g)), normalized by +1 on
a fixed base system (_igusa_base), from the theta transformation formula
(see above). With a common constant c for all S of genus g:
D(S) = c sum_C igusa_sign(g, S, C) theta[C].
"""
function igusa_sign(g::Int, S::Vector{Int}, C::Vector{Int})
  odds = [collect(c) for c in odd_theta_characteristics(g)]
  evens = [collect(c) for c in even_theta_characteristics(g)]
  S0, C0 = _igusa_base(g)
  return _igusa_sign(g, [odds[S0]; evens[C0]], [odds[sort(S)]; evens[C]])
end

# the sign for the ordered fundamental system F, base F0 (vectors)
function _igusa_sign(g::Int, F0, F)
  n = 2 * g
  V0 = reduce(hcat, [_f2(F0[i] .+ F0[end]) for i in 1:n])
  V = reduce(hcat, [_f2(F[i] .+ F[end]) for i in 1:n])
  L = _f2(V * _f2_inverse(V0))                    # linear part of the action on characteristics
  word = _transvection_word(_f2(transpose(_f2_inverse(L))), g)   # M mod 2 = L^-t
  kappa2, M = _kappa2_exponent(word, g)
  exponent = -kappa2
  sign = 1
  for (i, x) in enumerate(F0)
    image, phi8 = _igusa_action(M, x, g)
    @assert _f2(image) == F[i] "The transvections do not map the base system."
    exponent += i <= g ? phi8 : -phi8
    sign *= _reduction_sign(image, g)
  end
  exponent = mod(exponent, 8)
  @assert exponent in (0, 4) "Igusa sign: phase zeta_8^$exponent is not real."
  return exponent == 0 ? sign : -sign
end

@doc raw"""
    igusa_sign_table(g, sets) -> Dict

The signs of Igusa's formula for the sorted azygetic g-sets `sets`, from the
transformation formula (igusa_sign), in the format of
bracket_sign_table(...).table: S => (completions, signs). No samples needed;
the normalization (a global sign per genus) is that of the base system.
"""
function igusa_sign_table(g::Int, sets)
  odds, evens = _odd_masks(g), _even_masks(g)
  odd_vectors = [collect(c) for c in odd_theta_characteristics(g)]
  even_vectors = [collect(c) for c in even_theta_characteristics(g)]
  S0, C0 = _igusa_base(g)
  F0 = [odd_vectors[S0]; even_vectors[C0]]
  table = Dict{Vector{Int}, Tuple{Vector{Vector{Int}}, Vector{Int}}}()
  for S in sets
    S = sort(S)
    C = _fundamental_completions(g, odds[S], evens)
    table[S] = (C, [_igusa_sign(g, F0, [odd_vectors[S]; even_vectors[c]]) for c in C])
  end
  return table
end

@doc raw"""
    bracket_M_signs(setup) -> NamedTuple

The signs of the brackets of bracket_M from Igusa's transformation formula
(igusa_sign_table), in the format of learn_bracket_M_signs: no samples.
"""
function bracket_M_signs(setup)
  curve_sets, prym_sets = _bracket_M_sets(setup)
  return (curve = igusa_sign_table(5, curve_sets), prym = igusa_sign_table(4, prym_sets))
end

@doc raw"""
    compare_sign_tables(learned, derived) -> NamedTuple

Compares two sign tables (S => (completions, signs)) on their common sets:
the number of sets whose signs agree, are all opposite, or are neither (a
consistent pair of tables agrees up to one global sign: same or opposite on
all sets).
"""
function compare_sign_tables(learned, derived)
  same, opposite, inconsistent = 0, 0, 0
  for (S, (C, e)) in learned
    haskey(derived, S) || continue
    Cd, ed = derived[S]
    lookup = Dict(sort(c) => s for (c, s) in zip(Cd, ed))
    ratios = [s * lookup[sort(c)] for (c, s) in zip(C, e)]
    if all(==(1), ratios)
      same += 1
    elseif all(==(-1), ratios)
      opposite += 1
    else
      inconsistent += 1
    end
  end
  return (same = same, opposite = opposite, inconsistent = inconsistent)
end

################################################################################
#
#  Surveys of the bracket minors: the sample files, products and
#  hyperelliptic curves
#
################################################################################

@doc raw"""
    random_bracket_minors(count; seed = 1) -> Vector{NamedTuple}

`count` random 14 x 14 minors of bracket_M: 14 of the 20 rows, the 10 Prym
columns and 4 of the 15 curve columns.
"""
function random_bracket_minors(count::Int; seed::Int = 1)
  rng = Random.MersenneTwister(seed)
  return [(rows = sort(Random.randperm(rng, 20)[1:14]), columns = sort([collect(1:10); 10 .+ Random.randperm(rng, 15)[1:4]]))
          for _ in 1:count]
end

# For theta constant vectors x (balls): per minor log2 |minor| relative to the
# product of the largest entries of its rows (the radius when the ball
# contains 0: an upper bound); NaN for a minor with a vanishing row. Also the
# number of rows of bracket_M that vanish.
_bracket_minor_evidence(x, setup, signs, minors) = _bracket_minor_evidence(bracket_M(x, setup, signs), minors)

function _bracket_minor_evidence(A::AbstractMatrix, minors)
  CC = parent(A[1, 1])
  row_log2 = [maximum(RSR._log2_abs(a) for a in A[i, :]) for i in 1:size(A, 1)]
  values = Float64[]
  zero_balls = Bool[]
  for m in minors
    if any(==(-Inf), row_log2[m.rows])
      push!(values, NaN)
      push!(zero_balls, true)
      continue
    end
    D = det(matrix(CC, A[m.rows, m.columns]))
    z = contains_zero(D)
    push!(values, (z ? RSR._log2_radius(D) : RSR._log2_abs(D)) - sum(row_log2[m.rows]))
    push!(zero_balls, z)
  end
  return (values = values, zero_balls = zero_balls, zero_rows = count(==(-Inf), row_log2))
end

# One line per point: the largest value over the minors (and whether all of
# them are balls containing 0) and the smallest. (Not _evidence_line: that
# is the classification line of ReconstructGenusGTests.jl.)
function _minor_evidence_line(e)
  finite = filter(!isnan, e.values)
  isempty(finite) && return "all minors have a vanishing row ($(e.zero_rows) zero rows)"
  return string("minors: largest 2^", round(maximum(finite), digits = 1), all(e.zero_balls) ? " (all contain 0)" : "",
                ", smallest 2^", round(minimum(finite), digits = 1),
                e.zero_rows > 0 ? ", $(e.zero_rows) zero rows" : "")
end

@doc raw"""
    bracket_minor_survey(files, setup, signs, minors; min_bits = 250, sign_data = nothing,
                         verbose = true) -> Vector{NamedTuple}

The minors (random_bracket_minors, choose_bracket_minor) of bracket_M at full
precision on all samples of the files of sample_theta_data with at least
`min_bits` bits and determined signs (also those marked invalid by the old
rule). A sample counts as vanishing if all minors are below 2^(-bits/2).
Prints a line per sample (verbose) and a summary per (kind, type): the
number of samples, how many vanish, and the largest (Jacobians) resp.
smallest (others) value of the largest minor relative to -bits.
"""
function bracket_minor_survey(files, setup, signs, minors; min_bits::Int = 250, sign_data = nothing,
                              verbose::Bool = true)
  data4 = _loaded_sign_data(sign_data, 4)
  samples = filter(s -> s[:bits] >= min_bits && get(s, :signs_sufficient, "true") == "true",
                   load_theta_data(files; valid_only = false))
  out = NamedTuple[]
  for (k, s) in enumerate(samples)
    e = try
      _bracket_minor_evidence(_sample_theta_vectors(s, data4), setup, signs, minors)
    catch err
      err isa InterruptException && rethrow()
      verbose && println("sample $k: error ", first(sprint(showerror, err), 120))
      continue
    end
    finite = filter(!isnan, e.values)
    largest = isempty(finite) ? NaN : maximum(finite)
    vanishes = !isnan(largest) && largest < -s[:bits] / 2
    push!(out, (kind = s[:kind], type = s[:type], bits = s[:bits], largest = largest, vanishes = vanishes,
                evidence = e))
    verbose && println("sample $k: $(s[:kind]) $(s[:type]), $(s[:bits]) bits, ", _minor_evidence_line(e))
  end
  println("summary:")
  for key in unique((r.kind, r.type) for r in out)
    rs = filter(r -> (r.kind, r.type) == key, out)
    margins = [r.largest + r.bits for r in rs if !isnan(r.largest)]
    println("  $(key[1]) $(key[2]): $(length(rs)) samples, $(count(r -> r.vanishes, rs)) vanish; ",
            "largest minor + bits from ", round(minimum(margins), digits = 1), " to ", round(maximum(margins), digits = 1))
  end
  return out
end

# theta constant vectors (curve, Prym by Schottky-Jung with corrected signs)
# at a period matrix
# (reduce = false keeps the coordinates, so that eta = (0..0; 1 0..0) stays
# where the construction of tau put it)
function _tau_theta_vectors(tau::AcbMatrix, data4; reduce::Bool = false)
  t = reduce ? Hecke.siegel_reduction(tau)[2] : tau
  th = Hecke.thetas([zero(base_ring(t)) for _ in 1:nrows(t)], t)
  return _sample_theta_vectors(Dict{Symbol, Any}(:thetas => th), data4), th
end

@doc raw"""
    bracket_minor_special_points(setup, signs, minors; prec = 400, hyperelliptic = 3,
                                 partitions = [[1, 4], [4, 1], [2, 3], [3, 2], [1, 1, 3], [3, 1, 1], [1, 2, 2], [2, 2, 1]],
                                 products = 2, reduce = false, sign_data = nothing, seed = 1,
                                 verbose = true) -> Vector{NamedTuple}

The minors of bracket_M at hyperelliptic curves of genus 5 and at products
(product_period_matrix: of Jacobians, in the closure of J_5, and with
`jacobians = false`, random factors: for a factor of dimension 4 not in the
closure). Per point the number of vanishing even theta constants, of zero
rows of bracket_M, and the values of the minors (or the error, e.g. when the
Prym signs cannot be determined). Without `reduce` the period matrices are
not Siegel reduced, so eta = (0..0; 1 0..0) lies in the first block of the
partition ([1, 4]: in the elliptic curve, [4, 1]: in the 4-dimensional
factor).
"""
function bracket_minor_special_points(setup, signs, minors; prec::Int = 400, hyperelliptic::Int = 3,
                                      partitions = [[1, 4], [4, 1], [2, 3], [3, 2], [1, 1, 3], [3, 1, 1], [1, 2, 2],
                                                    [2, 2, 1]],
                                      products::Int = 2, reduce::Bool = false, sign_data = nothing, seed::Int = 1,
                                      verbose::Bool = true)
  Random.seed!(seed)
  data4 = _loaded_sign_data(sign_data, 4)
  out = NamedTuple[]
  function run(label, make_tau)
    t0 = time()
    result = try
      tau = make_tau()
      x, th = _tau_theta_vectors(tau, data4; reduce = reduce)
      vanishing = count(v -> RSR._safe_log2(RSR._abs64(v)) < -prec / 2, x.thetas)
      e = _bracket_minor_evidence(x, setup, signs, minors)
      (label = label, vanishing_thetas = vanishing, evidence = e, error = nothing)
    catch err
      err isa InterruptException && rethrow()
      (label = label, vanishing_thetas = -1, evidence = nothing, error = first(sprint(showerror, err), 150))
    end
    push!(out, result)
    verbose && println(rpad(label, 30), result.error === nothing ?
                       "$(result.vanishing_thetas) vanishing theta constants, " * _minor_evidence_line(result.evidence) :
                       "error: $(result.error)", " [", round(time() - t0, digits = 1), " s]")
  end
  for i in 1:hyperelliptic
    run("hyperelliptic $i", () -> begin
      RS = RSR.riemann_surface(hyperelliptic_test_curve(5), prec)
      _small_period_matrix(RSR.big_period_matrix(RS))
    end)
  end
  for partition in partitions, jacobians in (true, false), i in 1:products
    !jacobians && maximum(partition) <= 3 && continue    # the same as with Jacobians
    run("product $(join(partition, "+"))$(jacobians ? "" : " (random)") $i",
        () -> first(product_period_matrix(partition, prec; jacobians = jacobians, reduce = reduce)))
  end
  return out
end

################################################################################
#
#  Intersecting over eta at products E x B
#
#  At tau0 = diag(tau_E, tau_B) the matrix M of eta collapses to rank <= 10
#  when eta lies in E[2] (the Prym is B), for every B: the product locus
#  A_1 x A_4 lies in the zero locus of the minors of that eta. For eta with
#  nonzero component in B, rk M = 1 + rk M_4(B, eta_B) (the genus 4
#  construction for B), expected <= 12 only for B in the closure of J_4. Two
#  eta with Weil pairing 0 never both lie in E[2], so the common zero locus
#  of the minors of their matrices should meet A_1 x A_4 only in E x J_4.
#
#  The construction always uses eta = (0..0; 1 0..0) in the coordinates of
#  the period matrix. For a unimodular A, the characteristic [a; b] at
#  A tau0 A^t is [A^t a; A^-1 b] at tau0, so A tau0 A^t realizes eta =
#  (0; A^-1 e_1) of tau0: e_1 (elliptic), e_2 (in B), e_1 + e_2 (mixed),
#  pairwise orthogonal.
#
################################################################################

# A with A^-1 e_1 = the b-part of eta at tau0 = diag(tau_E, tau_B)
function _eta_transform(kind::Symbol)
  A = Matrix{Int}(RSR.LinearAlgebra.I, 5, 5)
  if kind === :abelian
    A[[1, 2], :] = A[[2, 1], :]
  elseif kind === :mixed
    A[2, 1] = -1
  else
    @req kind === :elliptic "Unknown kind of eta: $kind (:elliptic, :abelian, :mixed)."
  end
  return A
end

# bracket_M with the entries below 2^(-prec/2) relative to the largest entry
# (or balls containing 0) set to 0: at products whole rows and columns
# vanish analytically but are 2^-3000 numerically, and the minors relative
# to the row maxima would only see the rounding noise of such rows. Also the
# number of zero rows and columns and the numerical rank (Float64 SVD of the
# cleaned matrix with its rows and columns normalized) with the singular
# values around it (log10, relative).
function _clean_bracket_M(A, prec::Int)
  LA = RSR.LinearAlgebra
  CC = parent(A[1, 1])
  logs = [contains_zero(a) ? -Inf : RSR._log2_abs(a) for a in A]
  top = maximum(logs)
  top == -Inf && return (matrix = [zero(CC) for _ in A], zero_rows = size(A, 1), zero_columns = size(A, 2),
                         rank = 0, singular_values_log10 = Float64[])
  keep = logs .>= top - prec / 2
  C = [keep[i, j] ? A[i, j] : zero(CC) for i in 1:size(A, 1), j in 1:size(A, 2)]
  rows = [i for i in 1:size(A, 1) if any(keep[i, :])]
  columns = [j for j in 1:size(A, 2) if any(keep[:, j])]
  scale = inv(CC(2)^Int(round(top)))
  F = [keep[i, j] ? RSR._c64(A[i, j] * scale) : 0.0im for i in rows, j in columns]
  rank, sv = 0, Float64[]
  if !isempty(F)
    F = F ./ [LA.norm(F[i, :]) for i in 1:size(F, 1)]
    F = F ./ transpose([LA.norm(F[:, j]) for j in 1:size(F, 2)])
    s = LA.svdvals(F)
    rank = count(>(1e-12 * s[1]), s)
    sv = round.(log10.(max.(s ./ s[1], 1e-300)), digits = 1)
  end
  return (matrix = C, zero_rows = size(A, 1) - length(rows), zero_columns = size(A, 2) - length(columns),
          rank = rank, singular_values_log10 = sv)
end

@doc raw"""
    bracket_minor_eta_intersection(; setup_seeds = 1:3, minors_per_setup = 10, prec = 400,
                                   products = 2, jacobians = (true, false),
                                   etas = (:elliptic, :abelian, :mixed), max_free = 10,
                                   random_signs = 32, sign_data = nothing, seed = 1,
                                   verbose = true) -> Vector{NamedTuple}

At products tau0 = diag(tau_E, tau_B) (product_period_matrix([1, 4]; not
reduced; B a Jacobian of genus 4, in the closure of J_5, or with `jacobians`
false a random point of A_4) the minors of bracket_M for the pairwise
orthogonal eta in E[2] (:elliptic), in B[2] (:abelian) and mixed, realized
as A tau0 A^t (_eta_transform). Per setup (bracket_M_setup(seed = s),
bracket_M_signs, random_bracket_minors) the minors are evaluated for every
completion of the Prym signs that Riemann's relations leave free
(sign_completions; at most 2^max_free, otherwise `random_signs` random
ones). The minors are defined up to these signs, so a point lies in the
zero locus of the minors of an eta if they vanish (all below 2^(-prec/2))
for some completion: reported are the best (smallest) and worst value over
the completions of the largest minor, the numerical rank of bracket_M and
its zero rows and columns (_clean_bracket_M: entries below 2^(-prec/2)
relative to the largest are set to 0 first; zero columns come from
vanishing bracket forms of the setup, not from the geometry). On the Jacobian
locus the rank is at most 13.
"""
function bracket_minor_eta_intersection(; setup_seeds = 1:3, minors_per_setup::Int = 10, prec::Int = 400,
                                        products::Int = 2, jacobians = (true, false),
                                        etas = (:elliptic, :abelian, :mixed), max_free::Int = 10,
                                        random_signs::Int = 32, sign_data = nothing, seed::Int = 1,
                                        verbose::Bool = true)
  Random.seed!(seed)
  rng = Random.MersenneTwister(seed)
  data4 = _loaded_sign_data(sign_data, 4)
  setups = [(seed = s, setup = bracket_M_setup(seed = s)) for s in setup_seeds]
  setups = [(seed = t.seed, setup = t.setup, signs = bracket_M_signs(t.setup),
             minors = random_bracket_minors(minors_per_setup; seed = t.seed)) for t in setups]
  even5, even4 = even_theta_characteristics(5), even_theta_characteristics(4)
  out = NamedTuple[]
  for jac in jacobians, i in 1:products
    label = "E x " * (jac ? "J(C_4)" : "random B") * " $i"
    tau0 = try
      first(product_period_matrix([1, 4], prec; jacobians = jac, reduce = false))
    catch err
      err isa InterruptException && rethrow()
      verbose && println(label, ": error ", first(sprint(showerror, err), 150))
      continue
    end
    CC = base_ring(tau0)
    for kind in etas
      clock = time()
      record = try
        A = matrix(CC, _eta_transform(kind))
        tau = A * tau0 * transpose(A)
        th = Dict{NTuple{10, Int}, AcbFieldElem}(Tuple(c) => v for (c, v) in
                                                  Hecke.thetas([zero(CC) for _ in 1:5], tau))
        for c in odd_theta_characteristics(5)
          haskey(th, Tuple(c)) || (th[Tuple(c)] = zero(CC))
        end
        # theta constants that vanish at the product (balls around 0) set to
        # exactly 0: the square roots of Schottky-Jung would be indeterminate
        top = maximum(contains_zero(v) ? -Inf : RSR._log2_abs(v) for (_, v) in th)
        vanishing_curve = 0
        for c in collect(keys(th))
          v = th[c]
          if contains_zero(v) || RSR._log2_abs(v) < top - prec / 2
            th[c] = zero(CC)
            iseven(sum(c[1:5] .* c[6:10])) && (vanishing_curve += 1)
          end
        end
        curve = [th[Tuple(e)] for e in even5]
        pt = prym_thetas(5, th)
        vanishing_prym = count(e -> iszero(pt[Tuple(e)]), even4)
        sc = sign_completions(pt, 4, data4)
        bit_vectors = sc.free <= max_free ?
          [collect(Bool, b) for b in Iterators.product(ntuple(_ -> (false, true), sc.free)...)] :
          [rand(rng, Bool, sc.free) for _ in 1:random_signs]
        per_setup = NamedTuple[]
        for t in setups
          values = Float64[]
          undetermined = Int[]
          zero_columns = Int[]
          zero_rows = Int[]
          ranks = Int[]
          svs = Vector{Float64}[]
          for bits in bit_vectors
            tp = sc.completion(bits)
            x = (thetas = curve, thetas_prym = [tp[Tuple(e)] for e in even4])
            c = _clean_bracket_M(bracket_M(x, t.setup, t.signs), prec)
            e = _bracket_minor_evidence(c.matrix, t.minors)
            finite = filter(!isnan, e.values)    # NaN: a minor with a zero row
            push!(values, isempty(finite) ? -Inf : maximum(finite))
            push!(undetermined, count(e.zero_balls))
            push!(zero_columns, c.zero_columns)
            push!(zero_rows, c.zero_rows)
            push!(ranks, c.rank)
            push!(svs, c.singular_values_log10)
          end
          best, worst = minimum(values), maximum(values)
          push!(per_setup, (seed = t.seed, best = best, worst = worst, vanishes = best < -prec / 2,
                            minors_containing_zero = extrema(undetermined),
                            zero_columns = extrema(zero_columns), zero_rows = extrema(zero_rows),
                            ranks = extrema(ranks), singular_values_log10 = svs[argmin(ranks)]))
        end
        (label = label, eta = kind, vanishing = (curve = vanishing_curve, prym = vanishing_prym),
         free_signs = sc.free, completions = length(bit_vectors),
         exhaustive = sc.free <= max_free, setups = per_setup, error = nothing)
      catch err
        err isa InterruptException && rethrow()
        (label = label, eta = kind, vanishing = nothing, free_signs = -1, completions = 0, exhaustive = false, setups = NamedTuple[],
         error = first(sprint(showerror, err), 150))
      end
      push!(out, record)
      if verbose
        if record.error !== nothing
          println(rpad("$label, eta $kind", 32), "error: $(record.error)")
        else
          println(rpad("$label, eta $kind", 32), "vanishing even theta constants $(record.vanishing.curve) ",
                  "(curve), $(record.vanishing.prym) (Prym); $(record.free_signs) free Prym signs, ",
                  record.completions, record.exhaustive ? " completions" : " random completions",
                  " [", round(time() - clock, digits = 1), " s]")
          for r in record.setups
            sv = r.singular_values_log10
            println("    setup $(r.seed): ", r.vanishes ? "VANISHES" : "nonzero ", "  largest minor best 2^",
                    round(r.best, digits = 1), ", worst 2^", round(r.worst, digits = 1),
                    " ($(r.minors_containing_zero[2])/$minors_per_setup balls contain 0)",
                    ", rank $(r.ranks[1] == r.ranks[2] ? r.ranks[1] : r.ranks)",
                    " (zero rows $(r.zero_rows[2]), zero columns $(r.zero_columns[2]))",
                    ", singular values ", sv[max(1, r.ranks[1] - 3):min(end, r.ranks[1] + 2)])
          end
        end
      end
    end
  end
  if verbose
    println("summary (per point: the eta whose minors vanish, per setup):")
    for label in unique(r.label for r in out)
      rs = filter(r -> r.label == label && r.error === nothing, out)
      parts = String[]
      for s in setup_seeds
        v = [r.eta for r in rs if any(x -> x.seed == s && x.vanishes, r.setups)]
        push!(parts, "setup $s: " * (isempty(v) ? "none" : join(v, ", ")))
      end
      println("  ", rpad(label, 20), join(parts, "; "))
    end
  end
  return out
end

################################################################################
#
#  The bracket minors near special points
#
#  At the special points themselves theta constants vanish: the Prym signs
#  are not determined and balls around 0 lose all precision. Along
#  tau0 + t E (t = 2^-k) all theta constants are nonzero. E: a random
#  symmetric direction (generic points, not Jacobians) or the first order
#  smoothing of compact_type_degeneration (Jacobians up to O(t^2)); or the
#  period matrices of an actual degenerating family of curves
#  (approach_cusp_limit). The slope of log2 |minor| in k shows the order in
#  t with which the equations vanish at the special point.
#
################################################################################

function _random_symmetric_direction(g::Int, CC::AcbField)
  E = zero_matrix(CC, g, g)
  for i in 1:g, j in i:g
    E[i, j] = E[j, i] = CC(randn(), randn())
  end
  largest = maximum(RSR._abs64(E[i, j]) for i in 1:g for j in 1:g)
  return E * inv(CC(largest))
end

# minors along tau(t) for t = 2^-k
function _minor_path(label, taus, setup, signs, minors, data4; verbose::Bool = true)
  out = NamedTuple[]
  for (k, tau) in taus
    clock = time()
    record = try
      x, _ = _tau_theta_vectors(tau, data4)
      smallest = minimum(RSR._safe_log2(RSR._abs64(v)) for v in x.thetas) -
                 maximum(RSR._safe_log2(RSR._abs64(v)) for v in x.thetas)
      e = _bracket_minor_evidence(x, setup, signs, minors)
      finite = filter(!isnan, e.values)
      (label = label, k = k, smallest_theta_log2 = smallest, largest = isempty(finite) ? NaN : maximum(finite),
       evidence = e, error = nothing)
    catch err
      err isa InterruptException && rethrow()
      (label = label, k = k, smallest_theta_log2 = NaN, largest = NaN, evidence = nothing,
       error = first(sprint(showerror, err), 150))
    end
    push!(out, record)
    verbose && println(rpad("$label, t = 2^-$k", 36), record.error === nothing ?
                       "smallest theta 2^$(round(record.smallest_theta_log2, digits = 1)), " *
                       _minor_evidence_line(record.evidence) : "error: $(record.error)",
                       " [", round(time() - clock, digits = 1), " s]")
  end
  ok = filter(r -> r.error === nothing && !isnan(r.largest), out)
  if verbose && length(ok) >= 2
    slopes = [(ok[i+1].largest - ok[i].largest) / (ok[i+1].k - ok[i].k) for i in 1:length(ok)-1]
    println("    log2 of the largest minor per unit of k (minus the order in t): ", round.(slopes, digits = 2))
  end
  return out
end

@doc raw"""
    bracket_minor_product_approach(setup, signs, minors, partition; exponents = 4:4:32, prec = 800,
                                   random_factor = false, sign_data = nothing, seed = 1,
                                   verbose = true) -> Vector{NamedTuple}

The minors of bracket_M along tau0 + t E, t = 2^-k, at a product tau0 (not
reduced: eta = (0..0; 1 0..0) lies in the first block): with
compact_type_degeneration(partition) (Jacobians of curves of genus <= 4,
glued in a chain) in the smoothing direction (Jacobians up to O(t^2)) and in
a random direction (generic points); with `random_factor` (tau0 from
product_period_matrix(partition; jacobians = false), not in the closure of
J_5 for a factor of dimension 4) only in a random direction. Prints per t
the smallest theta constant (relative) and the minors, and the slopes.

Off the Jacobian locus (random directions, random factors) the theta
constants of the "Prym" by Schottky-Jung do not satisfy Riemann's relations,
so their signs, and bracket_M, are not defined (the sign search fails): the
minors are equations on the locus where Schottky-Jung gives theta constants
(Jacobians, Pryms), not on A_5. So the random direction is only tried with
`random_direction = true`.
"""
function bracket_minor_product_approach(setup, signs, minors, partition::Vector{Int}; exponents = 4:4:32,
                                        prec::Int = 800, random_factor::Bool = false, random_direction::Bool = false,
                                        sign_data = nothing,
                                        seed::Int = 1, verbose::Bool = true)
  Random.seed!(seed)
  data4 = _loaded_sign_data(sign_data, 4)
  CC = AcbField(prec)
  name = join(partition, "+")
  out = NamedTuple[]
  if random_factor
    tau0 = first(product_period_matrix(partition, prec; jacobians = false, reduce = false))
    E = _random_symmetric_direction(5, CC)
    append!(out, _minor_path("$name (random factor), random direction",
                             [(k, tau0 + CC(2)^(-k) * E) for k in exponents], setup, signs, minors, data4;
                             verbose = verbose))
  else
    c = compact_type_degeneration(partition, prec)
    E = _random_symmetric_direction(5, CC)
    append!(out, _minor_path("$name, smoothing", [(k, c.tau0 + CC(2)^(-k) * c.direction) for k in exponents],
                             setup, signs, minors, data4; verbose = verbose))
    random_direction && append!(out, _minor_path("$name, random direction",
                                                 [(k, c.tau0 + CC(2)^(-k) * E) for k in exponents],
                                                 setup, signs, minors, data4; verbose = verbose))
  end
  return out
end

@doc raw"""
    bracket_minor_hyperelliptic_approach(setup, signs, minors; exponents = 4:4:32, prec = 800,
                                         curve = nothing, sign_data = nothing, seed = 1,
                                         verbose = true) -> Vector{NamedTuple}

The minors of bracket_M along tau0 + t E, t = 2^-k, E random symmetric, at
the (not reduced) period matrix tau0 of a hyperelliptic curve of genus 5
(hyperelliptic_test_curve, or `curve`).
"""
function bracket_minor_hyperelliptic_approach(setup, signs, minors; exponents = 4:4:32, prec::Int = 800,
                                              curve = nothing, sign_data = nothing, seed::Int = 1,
                                              verbose::Bool = true)
  Random.seed!(seed)
  data4 = _loaded_sign_data(sign_data, 4)
  F = curve === nothing ? hyperelliptic_test_curve(5) : curve
  RS = RSR.riemann_surface(F, prec)
  tau0 = _small_period_matrix(RSR.big_period_matrix(RS))
  CC = base_ring(tau0)
  E = _random_symmetric_direction(5, CC)
  verbose && println("hyperelliptic curve ", F)
  return _minor_path("hyperelliptic, random direction", [(k, tau0 + CC(2)^(-k) * E) for k in exponents],
                     setup, signs, minors, data4; verbose = verbose)
end

@doc raw"""
    bracket_minor_on_family(r, setup, signs, minors; sign_data = nothing, verbose = true)
      -> Vector{NamedTuple}

The minors of bracket_M on the period matrices of an actual degenerating
family: the results of approach_cusp_limit (period matrices of curves) or
of approach_point / approach_hyperelliptic_locus (points projected to the
zero locus of Accola's equations near a special point, Jacobians if the
classification says so); field tau, Siegel reduced, so eta is not
controlled. On Jacobians the minors should stay at the precision.
"""
function bracket_minor_on_family(r, setup, signs, minors; sign_data = nothing, label = "family",
                                 verbose::Bool = true)
  data4 = _loaded_sign_data(sign_data, 4)
  # approach_cusp_limit: (k, status :ok, tau); approach_point (also
  # approach_hyperelliptic_locus): (t, status, tau)
  exponent(x) = hasproperty(x, :k) ? x.k : round(Int, -log2(x.t))
  taus = [(exponent(x), x.tau) for x in r.results if x.status !== :error && hasproperty(x, :tau)]
  return _minor_path(label, taus, setup, signs, minors, data4; verbose = verbose)
end

################################################################################
#
#  Intermediate Jacobians degenerating to hyperelliptic Jacobians
#
#  The chordal cubic S = det [x0 x1 x2; x1 x2 x3; x2 x3 x4] (the secant
#  variety of the rational normal quartic Gamma) and X_t = S + t F, F a
#  random cubic containing the line l = <e0, e4> (a secant line of Gamma).
#  IJ(X_t) tends to the Jacobian of the hyperelliptic curve branched over
#  Gamma . F (12 points; Collino). Projecting from l, X_t is a conic bundle
#  over P^2 (x1 : x2 : x3) with discriminant quintic Delta_t and an odd eta
#  (Beauville): IJ(X_t) = Prym(Delta_t, eta). Delta_0 = x2 (x2^2 - x1 x3)^2 / 4
#  (a line and a double conic). The eta of the conic bundle is not known in
#  theta coordinates; it is taken as the eta whose Schottky-Jung values have
#  66 small even theta constants (as many as a hyperelliptic Jacobian of
#  genus 5 has) with the largest gap to the others, and moved to
#  (0..0; 1 0..0) by relabeling the theta constants with the transformation
#  formula (no new theta constants). Then the bracket minors of the genus 5
#  Prym for eta' in its big Schottky locus.
#
################################################################################

@doc raw"""
    chordal_cubic_quintic(t; seed = 1, coefficients = -3:3, transform_seed = 1) -> NamedTuple

The discriminant quintic of the conic bundle structure of X_t = S + t F
(S the chordal cubic, F a random cubic (seed) containing the line
x1 = x2 = x3 = 0) from that line, `discriminant` in x1, x2, x3 (polynomial
ring in x0, ..., x4), and `quintic` the affine plane quintic after a random
change of coordinates (transform_seed) such that Baker's basis applies (as
plane_quintic_test_curve).
"""
function chordal_cubic_quintic(t; seed::Int = 1, coefficients = -3:3, transform_seed::Int = 1)
  R, x = polynomial_ring(QQ, [:x0, :x1, :x2, :x3, :x4]; cached = false)
  S = det(matrix(R, 3, 3, [x[1], x[2], x[3], x[2], x[3], x[4], x[3], x[4], x[5]]))
  rng = Random.MersenneTwister(seed)
  F = zero(R)
  for i in 1:5, j in i:5, k in j:5
    all(l -> l in (1, 5), (i, j, k)) && continue     # F vanishes on the line
    F += QQ(rand(rng, coefficients)) * x[i] * x[j] * x[k]
  end
  G = S + QQ(t) * F
  on_base(p) = evaluate(p, [zero(R), x[2], x[3], x[4], zero(R)])
  half = QQ(1, 2)
  L00 = half * on_base(derivative(derivative(G, 1), 1))
  L01 = half * on_base(derivative(derivative(G, 1), 5))
  L11 = half * on_base(derivative(derivative(G, 5), 5))
  Q0 = half * on_base(derivative(G, 1))
  Q1 = half * on_base(derivative(G, 5))
  C = on_base(G)
  D = det(matrix(R, 3, 3, [L00, L01, Q0, L01, L11, Q1, Q0, Q1, C]))
  S2, (u, v) = polynomial_ring(QQ, [:x, :y]; cached = false)
  rng2 = Random.MersenneTwister(transform_seed)
  for _ in 1:200
    P = rand(rng2, -2:2, 3, 3)
    RSR.LinearAlgebra.det(P) == 0 && continue
    l = [P[i, 1] * u + P[i, 2] * v + P[i, 3] for i in 1:3]
    f = evaluate(D, [zero(S2), l[1], l[2], l[3], zero(S2)])
    total_degree(f) == 5 || continue
    length(RSR._newton_polygon_interior_points(f)) == 6 || continue
    RSR._baker_certified(f, 6) || continue
    return (discriminant = D, quintic = f, transform = P, cubic = F)
  end
  error("No coordinates found in which Baker's basis applies (is the quintic singular?).")
end

_char_from_mask(mask::Int, g::Int) = ntuple(i -> (mask >> (i - 1)) & 1, 2 * g)
_mask_from_char(c) = sum(Int(c[i]) << (i - 1) for i in eachindex(c))
_mask_parity_bits(mask::Int, g::Int) = isodd(count_ones((mask & (2^g - 1)) & (mask >> g)))

# The linear part [D -C; -B A] (mod 2) of the action of M on characteristics.
function _char_linear_part(M::Matrix{Int}, g::Int)
  A, B, C, D = M[1:g, 1:g], M[1:g, g+1:end], M[g+1:end, 1:g], M[g+1:end, g+1:end]
  return _f2([D -C; -B A])
end

# An integral symplectic M (at most two integral transvections) whose action
# on characteristics moves the 2-torsion point eta (a vector mod 2) to
# (0..0; 1 0..0).
function _eta_to_standard(eta::Vector{Int}, g::Int)
  target = [i == g + 1 ? 1 : 0 for i in 1:2*g]
  identity = Matrix{Int}(RSR.LinearAlgebra.I, 2 * g, 2 * g)
  eta == target && return identity
  vectors = [collect(_char_from_mask(m, g)) for m in 1:4^g-1]
  T = [_integral_transvection(v, g) for v in vectors]
  N = [_char_linear_part(t, g) for t in T]
  reached = Dict{Vector{Int}, Int}()
  for (i, n) in enumerate(N)
    w = _f2(n * eta)
    w == target && return T[i]
    haskey(reached, w) || (reached[w] = i)
  end
  # the linear parts are involutions mod 2
  for (j, n) in enumerate(N)
    w = _f2(n * target)
    haskey(reached, w) && return T[j] * T[reached[w]]
  end
  error("No symplectic map found (eta = 0?).")
end

# The theta constants at M.tau from those at tau (all 4^g characteristics,
# NTuple keys), up to the common factor kappa(M) det(C tau + D)^(1/2):
# theta[M.m](M tau) ~ e(phi_m(M)) theta[m](tau) (Igusa), reduced with
# theta[r + 2l] = (-1)^(r' . l'') theta[r].
function _transform_theta_constants(thetas, M::Matrix{Int}, g::Int)
  CC = parent(first(values(thetas)))
  zeta = [exp(const_pi(CC) * onei(CC) * k / 4) for k in 0:7]
  out = Dict{NTuple{2 * g, Int}, AcbFieldElem}()
  for mask in 0:4^g-1
    m = collect(_char_from_mask(mask, g))
    image, phi8 = _igusa_action(M, m, g)
    value = get(thetas, Tuple(m), zero(CC))
    out[Tuple(_f2(image))] = _reduction_sign(image, g) * zeta[mod(phi8, 8) + 1] * value
  end
  return out
end

# Per 2-torsion point eta of genus g (a vector mod 2): the products
# |theta[m] theta[m + eta]| over the pairs of even characteristics, sorted;
# the gap (log2) between the `count` smallest and the rest, and how far the
# rest spreads below the largest.
function _eta_vanishing_scores(thetas, g::Int; count::Int = 66, floor_log2 = -1e6)
  la = fill(floor_log2, 4^g)
  for mask in 0:4^g-1
    v = get(thetas, _char_from_mask(mask, g), nothing)
    v === nothing && continue
    l = contains_zero(v) ? floor_log2 : RSR._log2_abs(v)
    la[mask+1] = max(l, floor_log2)
  end
  evens = [m for m in 0:4^g-1 if !_mask_parity_bits(m, g)]
  scores = NamedTuple[]
  for eta in 1:4^g-1
    values = Float64[]
    for m in evens
      n = xor(m, eta)
      (n > m && !_mask_parity_bits(n, g)) || continue
      push!(values, la[m+1] + la[n+1])
    end
    length(values) > count || continue
    sort!(values)
    top = values[end]
    push!(scores, (eta = collect(_char_from_mask(eta, g)), gap = values[count+1] - values[count],
                   small = values[count] - top, rest = values[count+1] - top, pairs = length(values)))
  end
  return sort!(scores; by = s -> -s.gap)
end

# the bracket minors (cleaned, see _clean_bracket_M) for theta vectors x
function _bracket_report(x, setup, signs, minors, prec::Int)
  c = _clean_bracket_M(bracket_M(x, setup, signs), prec)
  e = _bracket_minor_evidence(c.matrix, minors)
  finite = filter(!isnan, e.values)
  return (largest = isempty(finite) ? -Inf : maximum(finite), containing_zero = count(e.zero_balls),
          rank = c.rank, singular_values_log10 = c.singular_values_log10, zero_columns = c.zero_columns)
end

@doc raw"""
    chordal_cubic_family(; exponents = 2:2:10, prec = 800, seed = 1, coefficients = -3:3,
                         setup_seeds = 1:3, minors_per_setup = 10, limit_types = (10, 31, 36), eta_tries = 60,
                         curve_sign_data_6 = nothing, curve_sign_data_5 = nothing, sign_data_4 = nothing,
                         fay_relations_6 = nothing, check_transform = true, verbose = true)
      -> Vector{NamedTuple}

Along X_t = S + t F, t = 2^-k (chordal_cubic_quintic): the period matrix
and theta constants of the discriminant quintic (genus 6, `prec` bits); the
eta of the conic bundle, chosen by _eta_vanishing_scores (66 small
Schottky-Jung values, the largest gap; among the eta with kappa + eta odd,
kappa the odd characteristic with vanishing gradient, when the Fay kernel
finds it: Mumford's type of the intermediate Jacobians); the theta constants
relabeled so that eta = (0..0; 1 0..0) (_transform_theta_constants; with
`check_transform` compared once with theta constants computed at the
transformed period matrix); the genus 5 theta constants of IJ(X_t) by
Schottky-Jung. Then for one 2-torsion point eta' of genus 5 per limit type
(`limit_types`: the number of Schottky-Jung values that vanish in the
hyperelliptic limit, 10, 31, 36 for Prym J(H_4), E x J(H_3), J_2 x J_2) in
the big Schottky locus of IJ(X_t) (the standard one and random ones, moved
to the standard one in the same way; accepted when Riemann's relations
determine all signs of the genus 4 Schottky-Jung values and bracket_M has
rank at most 15) the
bracket minors per setup: the largest minor, the rank of bracket_M and its
singular values 11 to 16 (log10). In the hyperelliptic limit the rank of M
is 10, 13, 12 for the three types (hyperelliptic_eta_test.py), so for
t -> 0 the singular values beyond that should tend to 0.
"""
function chordal_cubic_family(; exponents = 2:2:10, prec::Int = 800, seed::Int = 1, coefficients = -3:3,
                              setup_seeds = 1:3, minors_per_setup::Int = 10, limit_types = (10, 31, 36),
                              eta_tries::Int = 60,
                              curve_sign_data_6 = nothing, curve_sign_data_5 = nothing, sign_data_4 = nothing,
                              fay_relations_6 = nothing, check_transform::Bool = true, verbose::Bool = true)
  data6 = _loaded_sign_data(curve_sign_data_6, 6)
  data5 = _loaded_sign_data(curve_sign_data_5, 5)
  data4 = _loaded_sign_data(sign_data_4, 4)
  setups = [(seed = s, setup = bracket_M_setup(seed = s)) for s in setup_seeds]
  setups = [(seed = t.seed, setup = t.setup, signs = bracket_M_signs(t.setup),
             minors = random_bracket_minors(minors_per_setup; seed = t.seed)) for t in setups]
  even5, even4 = even_theta_characteristics(5), even_theta_characteristics(4)
  odds6 = [collect(c) for c in odd_theta_characteristics(6)]
  rng = Random.MersenneTwister(seed)
  out = NamedTuple[]
  checked = !check_transform
  for k in exponents
    clock = time()
    record = try
      q = chordal_cubic_quintic(QQ(1, 2^k); seed = seed, coefficients = coefficients)
      RS = RSR.riemann_surface(q.quintic, prec; superelliptic = false, model = :original)
      tau6 = Hecke.siegel_reduction(_small_period_matrix(RSR.big_period_matrix(RS)))[2]
      @req nrows(tau6) == 6 "The quintic has genus $(nrows(tau6)), not 6."
      raw6 = _theta_constants_by_method(tau6, :riemann; curve_sign_data = data6, certified_fixed_signs = false)
      CC = base_ring(tau6)
      th6 = Dict{NTuple{12, Int}, AcbFieldElem}()
      for mask in 0:4^6-1
        c = _char_from_mask(mask, 6)
        th6[c] = _mask_parity_bits(mask, 6) ? zero(CC) : get(raw6, c, zero(CC))
      end
      bits6 = floor(Int, -RSR._log2_relative_radius([th6[Tuple(c)] for c in even_theta_characteristics(6)]))
      # kappa (Mumford's type), if the Fay kernel finds it
      kappa, kappa_gap = nothing, NaN
      try
        K, _ = odd_theta_gradient_kernel(6, th6; relations = fay_relations_6)
        norms = [RSR._safe_log2(maximum(RSR._abs64(K[r, c]) for c in 1:6)) for r in 1:nrows(K)]
        order = sortperm(norms)
        kappa, kappa_gap = odds6[order[1]], norms[order[2]] - norms[order[1]]
      catch err
        err isa InterruptException && rethrow()
      end
      scores = _eta_vanishing_scores(th6, 6; floor_log2 = -2.0 * prec)
      odd_type(s) = kappa === nothing || isodd(sum(_f2(kappa[1:6] .+ s.eta[1:6]) .* _f2(kappa[7:12] .+ s.eta[7:12])))
      candidates = filter(odd_type, scores)
      @req !isempty(candidates) "No eta of odd type."
      best = candidates[1]
      M6 = _eta_to_standard(best.eta, 6)
      new6 = _transform_theta_constants(th6, M6, 6)
      check = NaN
      if !checked
        # the relabeled theta constants against theta constants at the
        # transformed period matrix (M or its inverse, whichever convention
        # Hecke uses), up to a common factor
        checked = true
        devs = Float64[]
        top6 = maximum(RSR._log2_abs(v) for v in values(new6) if !contains_zero(v))
        keys_big = [c for c in keys(new6) if !_mask_parity_bits(_mask_from_char(c), 6) &&
                    !contains_zero(new6[c]) && RSR._log2_abs(new6[c]) > top6 - 20]
        for Mx in (M6, round.(Int, inv(Rational{BigInt}.(M6))))
          direct = Hecke.thetas([zero(CC) for _ in 1:6], Hecke.siegel_transform(matrix(ZZ, Mx), tau6))
          dd = Dict(Tuple(c) => v for (c, v) in direct)
          ratios = [RSR._c64(dd[c] / new6[c]) for c in keys_big]
          push!(devs, log2(maximum(abs.(ratios .- ratios[1])) / abs(ratios[1]) + 1e-300))
        end
        check = minimum(devs)
      end
      thetas5, sufficient5 = _prym_theta_constants(6, new6, data5)
      bits5 = floor(Int, -RSR._log2_relative_radius([thetas5[Tuple(c)] for c in even5]))
      # eta' of genus 5 in the big Schottky locus of IJ(X_t), one per limit
      # type: at a hyperelliptic curve of genus 5 the Prym of eta' is
      # J(hyperelliptic of genus 4), E x J(hyperelliptic of genus 3) or
      # J_2 x J_2 (Mumford), with 10, 31 and 36 vanishing even theta
      # constants; the type of eta' is read off from the largest gap in the
      # sorted Schottky-Jung values at these positions. An eta' whose
      # bracket_M has rank > 15 is not in the Schottky-Jung locus (the signs
      # are "determined" but the values are no theta constants): rejected.
      reports = NamedTuple[]
      rejected = 0
      tried = 0
      filled = Set{Int}()
      while length(filled) < length(limit_types) && tried < eta_tries
        tried += 1
        eta5 = tried == 1 ? [i == 6 ? 1 : 0 for i in 1:10] : rand(rng, 0:1, 10)
        iszero(eta5) && continue
        th5 = _transform_theta_constants(thetas5, _eta_to_standard(eta5, 5), 5)
        top = maximum(contains_zero(v) ? -Inf : RSR._log2_abs(v) for (_, v) in th5)
        for c in collect(keys(th5))
          v = th5[c]
          (contains_zero(v) || RSR._log2_abs(v) < top - bits5 / 2) && (th5[c] = zero(CC))
        end
        pt = prym_thetas(5, th5)
        logs = sort([contains_zero(pt[Tuple(e)]) ? -2.0 * prec : RSR._log2_abs(pt[Tuple(e)]) for e in even4])
        gaps = [logs[n+1] - logs[n] for n in limit_types]
        type_index = argmax(gaps)
        n_small = limit_types[type_index]
        n_small in filled && continue
        sc = sign_completions(pt, 4, data4)
        sc.free == 0 || continue
        tp = sc.completion(Bool[])
        x = (thetas = [th5[Tuple(e)] for e in even5], thetas_prym = [tp[Tuple(e)] for e in even4])
        per_setup = [(seed = s.seed, report = _bracket_report(x, s.setup, s.signs, s.minors, bits5)) for s in setups]
        if any(r.report.rank > 15 for r in per_setup)
          rejected += 1
          continue
        end
        push!(filled, n_small)
        push!(reports, (eta = eta5, small = n_small, gap = gaps[type_index], small_log2 = logs[n_small] - logs[end],
                        setups = per_setup))
      end
      (k = k, status = :ok, bits6 = bits6, bits5 = bits5, kappa = kappa, kappa_gap = kappa_gap, eta = best.eta,
       eta_gap = best.gap, eta_small = best.small, eta_rest = best.rest,
       runner_up_gap = length(candidates) > 1 ? candidates[2].gap : NaN, transform_check_log2 = check,
       signs5_sufficient = sufficient5, eta5_tried = tried, eta5_rejected = rejected, prym = reports, error = nothing)
    catch err
      err isa InterruptException && rethrow()
      (k = k, status = :error, error = first(sprint(showerror, err), 200))
    end
    push!(out, record)
    if verbose
      if record.status === :error
        println("t = 2^-$k: error: $(record.error) [", round(time() - clock, digits = 1), " s]")
      else
        r = record
        println("t = 2^-$k: genus 6 thetas to $(r.bits6) bits, genus 5 to $(r.bits5) bits",
                r.kappa === nothing ? ", kappa not found" : ", kappa gap 2^$(round(r.kappa_gap, digits = 1))",
                "; eta $(r.eta): gap at 66 2^$(round(r.eta_gap, digits = 1)) (next best ",
                "2^$(round(r.runner_up_gap, digits = 1))), 66 smallest <= 2^$(round(r.eta_small, digits = 1)), ",
                "rest >= 2^$(round(r.eta_rest, digits = 1)) (relative)",
                isnan(r.transform_check_log2) ? "" : "; relabeling against direct thetas 2^$(round(r.transform_check_log2, digits = 1))",
                r.signs5_sufficient ? "" : "; genus 5 signs NOT determined",
                "; $(length(r.prym)) eta' in $(r.eta5_tried) tries, $(r.eta5_rejected) rejected (rank > 15) [",
                round(time() - clock, digits = 1), " s]")
        for p in sort(r.prym; by = p -> p.small)
          println("    eta' $(join(p.eta)): limit type $(p.small) small (gap 2^$(round(p.gap, digits = 1)), ",
                  "smallest <= 2^$(round(p.small_log2, digits = 1)) relative)")
          for s in p.setups
          rep = s.report
          sv = rep.singular_values_log10
          println("      setup $(s.seed): rank $(rep.rank), largest minor 2^",
                  round(rep.largest, digits = 1), rep.containing_zero > 0 ? " ($(rep.containing_zero) balls contain 0)" : "",
                  ", singular values 11-16: ", sv[11:min(16, end)])
          end
        end
      end
    end
  end
  return out
end
