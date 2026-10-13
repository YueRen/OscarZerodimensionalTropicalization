using Revise
using Oscar
using OscarZerodimensionalTropicalization

n = 5

K,t = rational_function_field(QQ,:t);
# K,t = rational_function_field(GF(3),:t);
nu = tropical_semiring_map(K,t)

Kx,x = polynomial_ring(K,n);

f1 = (x[1] - sum([t^i for i in 0:n])) * (t*x[1] - sum([t^i for i in 0:n]))

F = [f1]
for j in 2:n
    if iseven(j)
        fj = (x[j]-x[j-1]+t^(j-2))*(x[j]-t*(x[j-1]+t^(-j+1)))
    else
        fj = (x[j]-x[j-1]+t^(j-2))*(t*x[j]-x[j-1]+t^(-j+1))
    end
    push!(F,fj)
end
I = ideal(F)
TropI = tropical_points_triangular(I, nu)
