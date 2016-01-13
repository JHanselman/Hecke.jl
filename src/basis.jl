function lll_basis_profile(rt_c::Hecke.roots_ctx, A::NfMaximalOrderIdeal; prec::Int = 100)
  c = Hecke.minkowski_mat(rt_c, Hecke.nf(order(A)), prec)
  l = lll(basis_mat(A))
  b = FakeFmpqMat(l)*basis_mat(order(A))
  if !isdefined(rt_c, :cache)
    rt_c.cache = 0*c
  end
  d = rt_c.cache
  Hecke.mult!(d, b.num, c)

  old = get_bigfloat_precision()
  set_bigfloat_precision(prec)

  g = Hecke.round_scale(d, prec)
  set_bigfloat_precision(old)
  g = g*g'
  Hecke.shift!(g, -prec)
  g += rows(g)*one(parent(g))

  l = lll_gram(g)

  lp = [ div(l[i,i], fmpz(2)^prec) for i=1:rows(l)]
  return lp
end

function short_elem(c::roots_ctx, A::NfMaximalOrderIdeal,
                v::fmpz_mat = MatrixSpace(FlintZZ, 1,1)(); prec::Int = 100)
  l, t = lll(c, A, v, prec = prec)
  w = window(t, 1,1, 1, cols(t))
  c = w*b
  q = elem_from_mat_row(K, c, 1, b_den)
  return q
end


function lll_basis(rt_c::Hecke.roots_ctx, A::NfMaximalOrderIdeal; 
                      v::fmpz_mat = MatrixSpace(FlintZZ, 1,1)(),
                      prec::Int = 100)
  K = nf(order(A))
  temp = FakeFmpqMat(basis_mat(A))*basis_mat(order(A))
  b = temp.num
  b_den = temp.den

  l, t = lll(rt_c, A, v, prec = prec)

  c = t*b
  q = nf_elem[elem_from_mat_row(K, c, i, b_den) for i=1:degree(K)]

  return q
end

function bkz_basis(rt_c::Hecke.roots_ctx, A::NfMaximalOrderIdeal, bs::Int; 
                      v::fmpz_mat = MatrixSpace(FlintZZ, 1,1)(),
                      prec::Int = 100)

                      
  K = nf(order(A))

  c = minkowski_mat(rt_c, K, prec)

  l, t1 = lll_with_transform(basis_mat(A))
  temp = FakeFmpqMat(l)*basis_mat(order(A))
  b = temp.num
  b_den = temp.den

  if !isdefined(rt_c, :cache)
    rt_c.cache = 0*c
  end
  d = rt_c.cache
  mult!(d, b, c)

  #ignore v

  g = round_scale(d, prec)

  #println("calling bkz")
  g, tt = bkz_trans(g, bs)  ## check: bkz_trans seems to s.t. kill the input

  c = tt*b
  q = nf_elem[elem_from_mat_row(K, c, i, b_den) for i=1:degree(K)]

  return q
end

function lll_basis(rt_c::Hecke.roots_ctx, A::NfMaximalOrderIdeal, bs::Int; 
                      v::fmpz_mat = MatrixSpace(FlintZZ, 1,1)(),
                      prec::Int = 100)

                      
  K = nf(order(A))

  c = minkowski_mat(rt_c, K, prec)

  @time l, t1 = lll_with_transform(basis_mat(A))
  @time temp = FakeFmpqMat(l)*basis_mat(order(A))
  b = temp.num
  b_den = temp.den

  if !isdefined(rt_c, :cache)
    rt_c.cache = 0*c
  end
  d = rt_c.cache
  @time mult!(d, b, c)

  #ignore v

  @time g = round_scale(d, prec)

  println("calling lll")
  @time g, tt = lll_with_transform(g)  ## check: bkz_trans seems to s.t. kill the input

  c = tt*b
  q = nf_elem[elem_from_mat_row(K, c, i, b_den) for i=1:degree(K)]

  return q
end

function fplll_basis(rt_c::Hecke.roots_ctx, A::NfMaximalOrderIdeal, bs::Int; 
                      v::fmpz_mat = MatrixSpace(FlintZZ, 1,1)(),
                      prec::Int = 100)
                      
  K = nf(order(A))

  c = minkowski_mat(rt_c, K, prec)

  @time l, t1 = lll_with_transform(basis_mat(A))
  @time temp = FakeFmpqMat(l)*basis_mat(order(A))
  b = temp.num
  b_den = temp.den

  if !isdefined(rt_c, :cache)
    rt_c.cache = 0*c
  end
  d = rt_c.cache
  @time mult!(d, b, c)

  #ignore v

  @time g = round_scale(d, prec)

  println("calling lll")
  @time g, tt = FPlll.lll_trans(g)  ## check: bkz_trans seems to s.t. kill the input

  c = tt*b
  q = nf_elem[elem_from_mat_row(K, c, i, b_den) for i=1:degree(K)]

  return q
end



function random_ideal_with_norm_up_to(a::Hecke.NfFactorBase, B::Integer)
  B = fmpz(B)
  O = order(a.ideals[1])
  K = Hecke.nf(O)
  I = Hecke.ideal(O, K(1))
  while B >= norm(a.ideals[end])
    J = a.ideals[rand(find(x -> (norm(x) <= B), a.ideals))]
    B = div(B, norm(J))
    I = I*J
  end
  return I
end



##chebychev_u ... in flint
function tschebyschew(Qx::Nemo.FmpqPolyRing, n::Int)
  T = [Qx(1), gen(Qx)]
  while length(T) <= n
    push!(T, 2*T[2]*T[end] - T[end-1])
  end
  return T[end]
end


function auto_of_maximal_real(K::AnticNumberField, n::Int)
  # image of zeta -> zeta^n
  # assumes K = Q(zeta+1/zeta)
  # T = tschebyschew(n), then
  # cos(nx) = T(cos(x))
  # zeta + 1/zeta = 2 cos(2pi/n)
  T = tschebyschew(parent(K.pol), n)
  i = evaluate(T, gen(K)*1//fmpz(2))*2
  return Mor(K, K, i)
end

function auto_simplify(A::Map, K::AnticNumberField)
  Qx = parent(K.pol)
  b = A(gen(K))
  return Mor(K, K, b)
end

function auto_power(A::Map, n::Int) 
  if n==1 
    return A
  end;
  B = x->A(A(x));
  C = auto_power(B, div(n, 2))
  if n%2==0
    return C
  else 
    return x-> A(C(x))
  end
end

function orbit(f::Map, a::Nemo.nf_elem)
  b = Set([a])
  nb = 1
  while true
    b = union(Set([f(x) for x in b]) , b)
    if nb == length(b)
      return b
    end
    nb = length(b)
  end
end


function order_of_auto(f::Map, K::AnticNumberField)
  a = gen(K)
  b = f(a)
  i = 1
  while b != a
    b = f(b)
    i += 1
  end
  return i
end


