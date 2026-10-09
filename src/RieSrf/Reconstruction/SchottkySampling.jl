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
    return reduce(hcat, columns)
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
Each line has `valid` (the theta constants known to at least prec/2 bits and
Accola's equations vanishing to half of that: they vanish on J_5 and on the
intermediate Jacobians, so this checks the theta constants and their signs),
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
samples as an uninterrupted one (an interrupted sample is redone). A curve
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
      accola_log2 = round(_max_log2(first(sign_pattern_relations(thetas, accola))), digits = 1)
      bits, values = _theta_values_string(thetas, 5)
      # Accola's equations vanish on J_5 and on the intermediate Jacobians of
      # cubic threefolds: a check of the theta constants (and their signs)
      valid = bits >= div(prec, 2) && accola_log2 < -div(bits, 2)
      (index = n, seed = sample_seed, kind = kind, status = :ok, valid = valid, curve = string(F),
       kappa = kappa === nothing ? "" : join(kappa, ","), type = type, verdict = verdict, stage = stage,
       accola_log2 = accola_log2, signs_sufficient = sufficient, prec = prec, bits = bits,
       time = round(time() - t0, digits = 1), thetas = values)
    catch err
      err isa InterruptException && rethrow()
      (index = n, seed = sample_seed, kind = kind, status = :error, error = sprint(showerror, err))
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
