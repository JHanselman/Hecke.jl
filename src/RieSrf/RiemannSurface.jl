################################################################################
#
#          RieSrf/RiemannSurface.jl : Riemann surfaces
#
# (C) 2022 Jeroen Hanselman
#
################################################################################

export RieSrf

export 

################################################################################
#
#  Types
#
################################################################################

mutable struct RiemannSurface
  defining_polynomial::PolyElem
  genus::Int
  small_period_matrix::arb_mat
  prec::Int
  embedding::Union{PosInf, InfPlc}
  

  function RiemannSurface(f::PolyElem,v::T, prec = 100) where T<:Union{PosInf, InfPlc}
    K = base_ring(f)
    
    RS = new()
    RS.defining_polynomial = f
    RS.prec = prec
    RS.embedding = v
    
    
  end

end


