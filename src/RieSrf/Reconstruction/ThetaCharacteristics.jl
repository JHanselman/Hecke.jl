################################################################################
#
#  ThetaCharacteristics.jl : theta characteristics and their transformations
#
#  A characteristic [a; b] (a, b in {0,1}^g) is stored as an NTuple of 2g bits
#  (a_1..a_g, b_1..b_g): the keys of the dictionaries of theta constants of
#  Hecke.thetas. It is even or odd with a.b. Used by all reconstruction files:
#
#   - enumeration of the characteristics, the index of a characteristic in the
#     output of acb_theta_all (char_to_index), the vanishing theta constants;
#   - the Schottky-Jung theta constants of the Prym for eta = (0..0; 1 0..0)
#     (prym_thetas) and the pairs of odd characteristics of the curve that
#     lie over an odd characteristic of the Prym (lift_prym_indices);
#   - the action of the symplectic group: over GF(2) on quadratic forms
#     (Aronhold systems, used by Riemann's and Fay's relations) and the
#     integral action on theta constants (Igusa's transformation formula),
#     used to move a 2-torsion point eta to the standard one.
#
################################################################################

# All theta constants theta[a, b](0, tau), keyed by tuples (a..., b...) in {0,1}^(2g)
function theta_constants(tau::AcbMatrix)
  CC = base_ring(tau)
  g = nrows(tau)
  return Hecke.thetas([zero(CC) for _ in 1:g], tau)
end

_is_even(ch) = iseven(sum(ch[i] * ch[i + div(length(ch), 2)] for i in 1:div(length(ch), 2)))

# The characteristics of genus g of the given parity, in the order of
# Iterators.product (this order numbers the rows of the gradient kernels).
function _theta_characteristics(g::Int, parity::Int)
  bits = Iterators.product(ntuple(_ -> 0:1, g)...)
  result = NTuple{2*g, Int}[]
  for a in bits, b in bits
    mod(sum(a[i] * b[i] for i in 1:g), 2) == parity && push!(result, (a..., b...))
  end
  return result
end

odd_theta_characteristics(g::Int) = _theta_characteristics(g, 1)
even_theta_characteristics(g::Int) = _theta_characteristics(g, 0)

# Even characteristics whose theta constant vanishes (relative to the largest
# one): |theta| < 2^(-prec/2) max |theta|.
function _vanishing_even_theta_constants(thetas::Dict{NTuple{N, Int64}, AcbFieldElem}, prec::Int) where N
  big = maximum(_log2abs(v) for v in values(thetas))
  return [ch for (ch, v) in thetas if _is_even(ch) && _log2abs(v) < big - prec/2]
end

# The position of a characteristic in the output of acb_theta_all, counted
# from 1 for (0..0, 1) with (0..0) last: the bits as a binary number, 0 -> 4^g.
char_to_index(char::Vector{QQFieldElem}) = char_to_index(map(x -> mod(x, 2), Int.(2*char)))
char_to_index(char::NTuple{N, Int}) where N = char_to_index(collect(char))

function char_to_index(char::Vector{Int})
  s = foldl((acc, x) -> (acc << 1) | x, char)
  return iszero(s) ? 2^length(char) : s
end

# The characteristic as a bit mask (bit i - 1 for entry i)
function bitmask(v::Vector{Int})
  m = zero(UInt128)
  for (i, x) in enumerate(v)
    iszero(x) || (m |= (UInt128(1) << (i - 1)))
  end
  return m
end

################################################################################
#
#  The Prym for eta = (0..0; 1 0..0)
#
################################################################################

# The odd characteristics delta of the Prym (genus g - 1) correspond to the
# pairs kappa = (0 d1; 0 d2), kappa + eta = (0 d1; 1 d2) of odd characteristics
# of the curve: their positions in odd_theta_characteristics(g).
function lift_prym_indices(g::Int)
  lifted = Dict(c => k for (k, c) in enumerate(odd_theta_characteristics(g)))
  return [(lifted[(0, d[1:g-1]..., 0, d[g:2*(g-1)]...)], lifted[(0, d[1:g-1]..., 1, d[g:2*(g-1)]...)])
          for d in odd_theta_characteristics(g - 1)]
end

@doc raw"""
    prym_thetas(g, thetas) -> Dict

The theta constants of the Prym variety of the double cover given by
eta = (0..0; 1 0..0) (genus g - 1) from those of the curve (genus g), by
Schottky-Jung (Farkas, Lemma 1, p. 148): theta_P[d]^2 is proportional to
theta[0 d1; 0 d2] theta[0 d1; 1 d2]. The square roots have arbitrary signs;
correct them with correct_signs_with_data!. The odd ones are 0.
"""
function prym_thetas(g::Int, thetas)
  CC = parent(first(values(thetas)))
  result = Dict{NTuple{2*(g-1), Int}, AcbFieldElem}()
  for d in even_theta_characteristics(g - 1)
    result[d] = sqrt(thetas[(0, d[1:g-1]..., 0, d[g:2*(g-1)]...)] *
                     thetas[(0, d[1:g-1]..., 1, d[g:2*(g-1)]...)])
  end
  for d in odd_theta_characteristics(g - 1)
    result[d] = zero(CC)
  end
  return result
end

################################################################################
#
#  The symplectic group over GF(2): quadratic forms and Aronhold systems
#
################################################################################

# The Gram matrix of the quadratic form of the characteristic (over GF(2))
function char_to_QF(char)
  g = div(length(char),2)
  id = identity_matrix(GF(2), g)
  zer = zero_matrix(GF(2), g, g)
  diag = diagonal_matrix(GF(2), char)
  J = [zer id ; zer zer]
  return J + diag
end

# A symplectic matrix over GF(2) that moves the quadratic form of char to its
# Arf normal form
function transform_to_arf_form(char)
  g = div(length(char),2)
  M = identity_matrix(GF(2), 2*g)
  J = collect(1:g)
  while length(J) != 0
    j = popfirst!(J)
    if char[j] == 0 && char[g+j] == 1
      M[j, g+j] = 1
    elseif char[j] == 1 && char[g+j] == 0
      M[g+j, j] = 1
    elseif char[j] == 1 && char[g+j] == 1
      I = findall(i -> char[i] == 1 && char[i+g] == 1, J)
      k = J[I[1]]
      filter!(x -> x != k, J)

      M[j, g + j] = 1
      M[k, j] = 1
      M[k, k] = 0
      M[k, g+j] = 1
      M[k, g+k] = 1
      M[g+j, k] = 1
      M[g+j, g+k] = 1
      M[g+k, k] = 1
    end
  end
  return M
end

# A symplectic matrix over GF(2) mapping the even characteristic char1 to char2
function map_even_characteristic(char1, char2)
  M1 = transform_to_arf_form(char1)
  M2 = transform_to_arf_form(char2)
  return M1 * inv(M2)
end

# The image of the characteristic char under the symplectic matrix M
function apply_transformation_to_char(M, char)
  im_QF = transpose(M) * char_to_QF(char) * M
  return  diagonal(im_QF)
end

# (e, d) for the half characteristics m = [e d], m2 = [e2 d2]: 4 e.d resp. 4 e.d2
function half_char_inner_prod(n::Vector{QQFieldElem})
  g = div(length(n),2)
  return Int(4*(transpose(n[1:g]) * n[g+1:2*g]))
end

function half_char_inner_prod(n::Vector{QQFieldElem}, m::Vector{QQFieldElem})
  g = div(length(n),2)
  return Int(4*(transpose(n[1:g]) * m[g+1:2*g]))
end

function half_char_inner_prod(n::Vector{FqFieldElem}, m::Vector{FqFieldElem})
  g = div(length(n),2)
  return Int(lift(ZZ,((transpose(n[1:g]) * m[g+1:2*g]))))
end

# A fundamental (azygetic) system of 2g + 1 characteristics (columns)
function azygetic_system(g::Int)
  zer = zero_matrix(GF(2), g, g)
  zer1 = zero_matrix(GF(2), g, 1)
  zer2 = zero_matrix(GF(2), g, 2)
  id = identity_matrix(GF(2), g)
  triang = zer
  for i in (1:g)
    for j in (i:g)
      triang[i,j] = 1
    end
  end

  odd_chars = [id; triang]
  even_chars = [[id zer2] ; [zer1 triang zer1]]

  return [odd_chars even_chars]
end

# The Aronhold system of genus g (2g + 1 characteristics, any three of them
# azygetic), moved by M
function aronhold_system(g::Int, M)
  a = aronhold_system(g)
  apply_transformation_to_char.(Ref(M), a)
end

function aronhold_system(g::Int)
  azy_set = azygetic_system(g)
  zer = zero_matrix(GF(2), g, g)
  id = identity_matrix(GF(2), g)
  J = [zer id; id zer]
  J1 = [zer id; zer zer]

  w = diagonal(transpose(azy_set) * J1 * azy_set)

  for i in (1:2*g+2)
    e = zeros(GF(2),2*g+2)
    e[i] += g
    test, sol = can_solve_with_solution(J*azy_set, w+e)
    if test
      return [t + sol for t in [transpose(azy_set)[j,:] for j in (1:ncols(azy_set))][(1:end) .!= i]]
    end
  end
  error("Error in computation of aronhold system.")

end

# The characteristics of the Max Noether relations built on the Aronhold
# system moved by M: L, the lambda_h, the a_rho and a_2g (halves)
function max_noether_data(g::Int, M)
  a = aronhold_system(g, M)
  a = [QQ.(lift.(Ref(ZZ), av))/2 for av in a]
  a0 = sum(a)


  l = Vector{QQFieldElem}[]
  for p in (1:g-3)
    push!(l, a[2*p+6] + a[2*p+7])
  end

  lambda = Vector{QQFieldElem}[]
  l_M = matrix(l)
  V = Iterators.product(repeat([[QQ(0),QQ(1)]], g-3)...)
  for v in V 
    v = [v...]
    push!(lambda, v * l_M)
  end

  L = sum(a[i] for i in (8:2:2*g))
  if mod(g, 2) == 1
    L += a0
  end
  return L, lambda, [[a0] ; a[1:7]], a[2*g]
end

function max_noether_characteristics(g::Int)
  L, lambda, A_rho, a2g = max_noether_data(g, identity_matrix(GF(2), 2*g))

  chars = []

  for h in (1:2^(g-3)) 
    v = L + lambda[h]
    push!(chars, v)
  end

  for a_rho in A_rho
    for j in (1:2^(g-4))
      v = L + lambda[j] + a_rho + a2g
      push!(chars, v)
    end
  end

  return chars
end

################################################################################
#
#  The integral symplectic group on theta constants
#
#  For M = [A B; C D] in Sp(2g, Z) and tau' = M tau = (A tau + B)(C tau + D)^-1
#  (Hecke.siegel_transform), Igusa's formula: theta[M.m](tau') is
#  e(phi_m(M)) theta[m](tau) times a factor that does not depend on m. Used
#  to change the symplectic basis so that a chosen 2-torsion point becomes
#  eta = (0..0; 1 0..0), the one of prym_thetas.
#
################################################################################

_f2(x) = mod.(x, 2)

_char_from_mask(mask::Int, g::Int) = ntuple(i -> (mask >> (i - 1)) & 1, 2 * g)

# The transvection x -> x + <x, v> v of Z^2g (symplectic)
function _integral_transvection(v::Vector{Int}, g::Int)
  J = [zeros(Int, g, g) Matrix{Int}(LinearAlgebra.I, g, g); -Matrix{Int}(LinearAlgebra.I, g, g) zeros(Int, g, g)]
  return Matrix{Int}(LinearAlgebra.I, 2 * g, 2 * g) + v * transpose(v) * J
end

# The linear part [D -C; -B A] (mod 2) of the action of M on characteristics
function _char_linear_part(M::Matrix{Int}, g::Int)
  A, B, C, D = M[1:g, 1:g], M[1:g, g+1:end], M[g+1:end, 1:g], M[g+1:end, g+1:end]
  return _f2([D -C; -B A])
end

# The image M.m (not reduced) of the characteristic m and 8 phi_m(M)
function _igusa_action(M::Matrix{Int}, m::Vector{Int}, g::Int)
  A, B, C, D = M[1:g, 1:g], M[1:g, g+1:end], M[g+1:end, 1:g], M[g+1:end, g+1:end]
  a, b = m[1:g], m[g+1:end]
  dCD = [sum(C[i, :] .* D[i, :]) for i in 1:g]
  dAB = [sum(A[i, :] .* B[i, :]) for i in 1:g]
  image = [D * a - C * b + dCD; -B * a + A * b + dAB]
  phi8 = -(a' * B' * D * a + b' * A' * C * b - 2 * a' * B' * C * b) + 2 * ((D * a - C * b)' * dAB)
  return image, phi8
end

# theta[r + 2l] = (-1)^(r' . l'') theta[r]: the sign of the reduction mod 2
function _reduction_sign(m::Vector{Int}, g::Int)
  r = _f2(m)
  l = (m[g+1:end] .- r[g+1:end]) .÷ 2
  return iseven(sum(r[1:g] .* l)) ? 1 : -1
end

# An integral symplectic M (at most two transvections) whose action on
# characteristics moves the 2-torsion point eta (a vector mod 2) to
# (0..0; 1 0..0)
function _eta_to_standard(eta::Vector{Int}, g::Int)
  target = [i == g + 1 ? 1 : 0 for i in 1:2*g]
  identity = Matrix{Int}(LinearAlgebra.I, 2 * g, 2 * g)
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

# The theta constants at M tau from those at tau (all characteristics), up to
# a common factor
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
