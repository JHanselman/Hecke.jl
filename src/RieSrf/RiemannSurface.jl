################################################################################
#
#          RieSrf/RiemannSurface.jl : Riemann surfaces
#
# (C) 2022 Jeroen Hanselman
#
################################################################################

export RieSrf

export RiemannSurface

################################################################################
#
#  Types
#
################################################################################

mutable struct RiemannSurface
  defining_polynomial::PolyElem
  genus::Int
  tau::acb_mat
  prec::Int
  embedding::Union{PosInf, InfPlc}
  

  function RiemannSurface(tau::acb_mat)
    RS = new()
    g = ncols(tau)
    if nrows(tau) != g
      error("Matrix needs to be a square matrix")
    end
    RS.genus = g
    prec = precision(parent(M[1,1]))
    RS.small_period_matrix = tau
  end

  #function RiemannSurface(f::PolyElem,v::T, prec = 100) where T<:Union{PosInf, InfPlc}
  #  K = base_ring(f)
    
  #  RS = new()
  #  RS.defining_polynomial = f
  #  RS.prec = prec
  #  RS.embedding = v
    
    
  #end

end

function small_period_matrix(RS)
  return tau
end


