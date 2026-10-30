# Exact test: is there an affine bijection x -> M x + c of GF(2)^2g (bit masks)
# preserving the parity of characteristics (i.e. an element of the affine
# action of Sp(2g, Z) on characteristics) with colA[x] == colB[phi(x)] for all x?
# colors: vectors indexed by mask + 1 (odd characteristics: any fixed color).
# Backtracking over the images of an affine basis, checking the whole affine
# span after each choice.
function sp_equivalent(colA::Vector, colB::Vector, g::Int; max_nodes::Int = 10^7)
  n = 2 * g
  N = 1 << n
  # affine basis of A: 0 and the unit vectors (as points of GF(2)^2g)
  base = [0; [1 << i for i in 0:n - 1]]
  byColor = Dict{Any, Vector{Int}}()
  for y in 0:N - 1
    push!(get!(byColor, colB[y + 1], Int[]), y)
  end
  for (i, x) in enumerate(base)
    length(get(byColor, colA[x + 1], Int[])) == count(==(colA[x + 1]), colA) || return false
  end
  nodes = 0
  img = zeros(Int, n + 1)
  # phi on the span of the first k basis vectors: phi(sum_{i in S} e_i) = c + sum M e_i
  function check(k)
    # c = img[1]; M e_i = img[i+1] xor c
    c = img[1]
    for s in 0:(1 << k) - 1
      # only subsets containing the new basis vector k
      (k == 0 || isodd(s >> (k - 1))) || continue
      x = 0; y = c
      for i in 1:k
        if isodd(s >> (i - 1))
          x |= 1 << (i - 1)
          y = xor(y, xor(img[i + 1], c))
        end
      end
      colA[x + 1] == colB[y + 1] || return false
    end
    return true
  end
  used = Set{Int}()
  function rec(k)
    nodes += 1
    nodes > max_nodes && error("too many nodes")
    if k > n
      c = img[1]
      M = [xor(img[i + 1], c) for i in 1:n]
      # M invertible over GF(2)
      span = Set{Int}([0])
      for v in M
        span = union(span, Set(xor(s, v) for s in span))
      end
      return length(span) == N
    end
    for y in byColor[colA[base[k + 1] + 1]]
      y in used && continue
      img[k + 1] = y
      # linear independence of the images of the vectors: M e_i distinct and independent
      check(k) || continue
      push!(used, y)
      rec(k + 1) && return true
      delete!(used, y)
    end
    return false
  end
  ok = rec(0)
  return ok
end
