using Revise
using Oscar
using OscarZerodimensionalTropicalization

n = 5

K,t = rational_function_field(QQ,:t);
# K,t = rational_function_field(GF(3),:t);
nu = tropical_semiring_map(K,t)

Kx,x = polynomial_ring(K,n);

f1 = (x[1] - 1) * (t*x[1] - 1)

F = [f1]
for j in 2:n
    fj = (x[j]-x[j-1])*(t*x[j]-x[j-1])
    push!(F,fj)
end
I = ideal(F)
TropI = tropical_points_triangular(I, nu)
