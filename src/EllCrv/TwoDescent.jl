###############################################################################
#
#  Two descent for elliptic curves
#
#
#  (C) 2022 Jeroen Hanselman
#
###############################################################################

export quartic_I_invariant, quartic_J_invariant, quartic_p_seminvariant, quartic_q_seminvariant, quartic_r_seminvariant, quartic_g4_covariant, quartic_g6_covariant

function two_selmer_group(E::EllCrv{T}) where T <: Union{fmpq, nf_elem}
  E, phi = short_weierstrass_model(E)
  E, psi = integral_model(E)
  
  P, _ = hyperelliptic_polynomials(E)
  dP = derivative(P)
  
  K = base_field(E)
  a = gen(K)
  L, theta = number_field(f, "theta")
  OK = ring_of_integers(K)
  OL = ring_of_integers(L)
  disc = OK(discriminant(f))*OK
  
  #For every prime p in OK such that p^2 divides disc(E)
  p_inK = [f for (f,e) in factor(disc) if e >2]
  
  S = []
  
  dP_theta = dP(theta)
  
  #Take all primes q above p in OL
  for p in p_inK
    for (q, e) in factor(p*OL)
      if (dP_theta in q)
        push!(S_finite, q)
      end
    end
  end
  
  UL = sunit_group(S_finite)
  
  
  
end


function quartic_I_invariant(q)
  a, b, c, d, e = quartic_coeffs(q)
  return 12*a*e - 3*b*d + c^2
end

function quartic_J_invariant(q::PolyElem)
  a, b, c, d, e = quartic_coeffs(q)
  return 72*a*c*e + 9*b*c*d - 27*a*d^2 - 27*e*b^2 - 2*c^3
end

function quartic_p_seminvariant(q::PolyElem)
  a, b, c, d, e = quartic_coeffs(q)
  return 3*b^2 - 8*a*c
end

function quartic_q_seminvariant(q::PolyElem)
  a, b, c, d, e = quartic_coeffs(q)
  p = quartic_p_seminvariant(q)
  I = quartic_I_invariant(q)
  return 1//3*(p^2 - 16*a^2*I)
end

function quartic_r_seminvariant(q::PolyElem)
  a, b, c, d, e = quartic_coeffs(q)
  return b^3 + 8*a^2*d - 4*a*b*c
end

function quartic_g4_covariant(q::PolyElem)
  Rx = parent(q)
  x = gen(Rx)
  a, b, c, d, e = quartic_coeffs(q)
  return (3*b^2 - 8*a*c)*x^4 + 4*(b*c - 6*a*d)*x^3 + 2*(2*c^2 - 24*a*e - 3*b*d)*x^2 + 4*(c*d - 6*b*e)*x +(3*d^2 - 8*c*e)
end

function quartic_g6_covariant(q::PolyElem)
  Rx = parent(q)
  x = gen(Rx)
  a, b, c, d, e = quartic_coeffs(q)
  return (b^3 + 8*a^2*d - 4*a*b*c)*x^6 + 2*(16*a^2*e + 2*a*b*d - 4*a*c^2 + b^2*c)*x^5 + 5*(8*a*b*e + b^2*d - 4*a*c*d)*x^4 + 20*(b^2*e - a*d^2)*x^3 - 5*(8*a*d*e + b*d^2 - 4*b*c*e)*x^2 - 2*(16*a*e^2 + 2*b*d*e - 4*c^2*e + c*d^2)*x - (d^3 + 8*b*e^2 - 4*c*d*e) 
end

function is_equivalent(q1::PolyElem, q2::PolyElem)
  if !(3<=degree(q1)<= 4) || !( 3<= degree(q2) <= 4)
    error("Polynomials must be of degree 3 or 4.")
  end
  return quartic_I_invariant(q1) == quartic_I_invariant(q2) && quartic_J_invariant(q1) == quartic_J_invariant(q2)
end

function quartic_coeffs(q)
  if !(3<=degree(q)<= 4)
    error("Polynomials must be of degree 3 or 4.")
  end
  a = coefficients(q)
  return a[4], a[3], a[2], a[1], a[0]
end
