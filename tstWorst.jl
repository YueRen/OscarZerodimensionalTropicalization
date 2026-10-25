using Revise
using Oscar
using OscarZerodimensionalTropicalization

set_verbosity_level(:ZerodimensionalTropicalization, 1)

n = 7

K,t = rational_function_field(QQ,:t);
# K,t = rational_function_field(GF(3),:t);
nu = tropical_semiring_map(K,t)

Kx,x = polynomial_ring(K,n);

#f1 = (x[1] - sum([t^i for i in 0:n])) * (t*x[1] - sum([t^i for i in 0:n]))

#F = [f1]
#for j in 2:n
#    if iseven(j)
#        fj = (x[j]-x[j-1]+t^(j-2))*(x[j]-t*(x[j-1]+t^(-j+1)))
#    else
#        fj = (x[j]-x[j-1]+t^(j-2))*(t*x[j]-x[j-1]+t^(-j+1))
#    end
#    push!(F,fj)
#end
#I = ideal(F)
#TropI = tropical_points_triangular(I, nu)
#println(TropI)

f1 = (x[1]^2- sum([t^i for i in 0:n+1]))


F = [f1]
for j in 2:n
    fj = (x[j]-(x[1]^2-sum([t^i for i in 0:j])))
    push!(F,fj)
end

I = ideal(F)
TropI = tropical_points_triangular(I, nu)
println(TropI)


## Terminates, but shouldn't the point be [0,infty]? Rather than [0,0]. 
n = 2 
Kx,x = polynomial_ring(K,n);
f1 = (x[1]^2- sum([t^i for i in 0:n]))
f2 = x[2]
F = [f1,f2]
I = ideal(F)
TropI = tropical_points_triangular(I, nu)
println(TropI)




