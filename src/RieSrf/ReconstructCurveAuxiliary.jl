
function _sign_flip(char::Vector{QQFieldElem})
  g = div(length(char), 2)
  v = [floor(QQFieldElem, c) for c in char]
  zer = zero_matrix(QQ, g, g)
  id = identity_matrix(QQ, g)
  J = [zer id; zer zer]
  result = (-1)^(Int(2*((transpose(char * J) * v))))
  return result
end


function theta_HI(D, char)
  newchar = mod.(Int.(2*char), Ref(2))
  return D[newchar...]*_sign_flip(char)
end

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

function theta_list(thetas, g)
  theta_indices = Hecke.theta_characteristics_indices(g)
  theta_list = [thetas[theta_indices[i + 1]] for i in (1:2^(2*g)-1)]
  push!(theta_list, thetas[theta_indices[1]])
  return theta_list
end


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

function char_to_QF(char)
  g = div(length(char),2)
	id = identity_matrix(GF(2), g)
  zer = zero_matrix(GF(2), g, g)
  diag = diagonal_matrix(GF(2), char)
	J = [zer id ; zer zer]
  return J + diag
end 

function map_even_characteristic(char1, char2)

  M1 = transform_to_arf_form(char1)
  M2 = transform_to_arf_form(char2)

  return M1 * inv(M2)
end

function apply_transformation_to_char(M, char)
  im_QF = transpose(M) * char_to_QF(char) * M
  return  diagonal(im_QF)
end

# Transvection T_u(x) = x + (x^T J u) u where J is the symplectic form
function transvection(u)
  g = div(length(u),2)
  id = identity_matrix(GF(2), g)
  zer = zero_matrix(GF(2), g, g)
	J = [zer id ; id zer]
  n = nrows(J)
  return identity_matrix(base_ring(J), n) + u * transpose(u) * J
end

# Generators for Stab(v) inside Sp(2g, F_2)
function stabilizer_generators(v, g)
    J = symplectic_form(g)
    ell = transpose(v) * J              # linear functional u -> <v,u>
    rk, N = nullspace(ell)              # columns of N span v^perp
    gens = [transvection(N[:, i], J) for i in 1:ncols(N)]
    return filter(M -> M != identity_matrix(GF(2), 2g), gens)
end