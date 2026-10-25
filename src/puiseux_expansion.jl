################################################################################
#
# Puiseux expansions (of univariate polynomials over uncertainty rings)
#
###############################################################################

function initial(f::Oscar.PuiseuxMPolyRingElem)
    if iszero(f)
        return zero(base_ring(parent(f)))
    end
    C = collect(coefficients(f))
    return last(C)
end

@doc raw"""
    has_non_constant_coefficients(fTilde::MPolyRingElem{<:MPolyRingElem{<:PuiseuxMPolyRingElem}})

Given a polynomial `fTilde` in $K[u_1,...,u_n][x_1,...,x_n]$, return `true` if
`fTilde` has coefficients in $K[u_1,...,u_n]\setminus K$.  Return `false` if all
coefficients lie in $K$.

# Examples
```jldoctest
julia> K = algebraic_closure(QQ);

julia> Kt,(t,) = puiseux_polynomial_ring(K,["t"]);

julia> Ktu,(u1,u2,u3) = polynomial_ring(Kt,[:u1,:u2,:u3]);

julia> Ktux,(x1,x2,x3) = polynomial_ring(Ktu,[:x1,:x2,:x3]);

julia> f1Tilde = t + 2*x1 + 2*x1^2; # coefficients constant

julia> has_non_constant_coefficients(f1Tilde)
false

julia> f2Tilde = (t+u1*t^2) + x2 + x2^2; # coefficients contain u

julia> has_non_constant_coefficients(f2Tilde)
true

```
"""
function has_non_constant_coefficients(fTilde::MPolyRingElem{<:MPolyRingElem{<:PuiseuxMPolyRingElem}})
    for xCoeff in coefficients(fTilde)
        if any(!iszero, exponents(xCoeff))
            return true
        end
    end
    return false
end



@doc raw"""
    initial_zero(fTilde::MPolyRingElem{<:MPolyRingElem{<:PuiseuxMPolyRingElem}})

Given a polynomial `fTilde` in $K[u_1,...,u_n][x_1,...,x_n]$, return the initial
of `fTilde` with respect to weight vector $(0,...,0)$.

# Examples
```jldoctest
julia> K = algebraic_closure(QQ);

julia> Kt,(t,) = puiseux_polynomial_ring(K,["t"]);

julia> Ktu,(u1,u2,u3) = polynomial_ring(Kt,[:u1,:u2,:u3]);

julia> Ktux,(x1,x2,x3) = polynomial_ring(Ktu,[:x1,:x2,:x3]);

julia> f1Tilde = t + 2*x1 + 2*x1^2;

julia> initial_zero(f1Tilde) # no constant term as it had valuation 1
{a1: 2.00000}*x1^2 + {a1: 2.00000}*x1

julia> f2Tilde = (1+t+u1*t^2) + x2 + x2^2; # higher order terms are dropped

julia> initial_zero(f2Tilde)
{a1: 1.00000}*x2^2 + {a1: 1.00000}*x2 + {a1: 1.00000}

```
"""
function initial_zero(fTilde::MPolyRingElem{<:MPolyRingElem{<:PuiseuxMPolyRingElem}})
    # iterate over all x-coefficients (polynomials in u),
    # iterate over all u-coefficients (puiseux polynomials),
    # and record all valuations found. find the minimal one
    allVals = [ valuation.(coefficients(xCoeff)) for xCoeff in coefficients(fTilde) ]
    minVal = minimum(Iterators.flatten(allVals))

    # return sum over all monomials of lowest valuation,
    # replacing the puiseux polynomial coefficients by their initial
    Ktux = parent(fTilde)
    Ktu = base_ring(Ktux)
    Kt = base_ring(Ktu)
    zeroInitial = zero(Ktux)
    for (xMon, xCoeff, xCoeffVals) in zip(monomials(fTilde), coefficients(fTilde), allVals)
        for (uMon, uCoeff, uCoeffVal) in zip(monomials(xCoeff), coefficients(xCoeff), xCoeffVals)
            if uCoeffVal == minVal
                zeroInitial += Kt(initial(uCoeff)) * uMon * xMon # todo: check why Kt() is necessary
            end
        end
    end
    return zeroInitial
end


@doc raw"""
    convert_for_roots_in_puiseux_expansion(h::MPolyRingElem{<:MPolyRingElem{<:PuiseuxMPolyRingElem}})

Convert polynomial `h` in $K[x_i]\subseteq K{{t}}[u_1,\dots,u_n][x_1,\dots,x_n]$
to a polynomial in $K[x_i]$.

# Examples
```jldoctest
julia> K = algebraic_closure(QQ);

julia> Kt,(t,) = puiseux_polynomial_ring(K,["t"]);

julia> Ktu,(u1,u2,u3) = polynomial_ring(Kt,[:u1,:u2,:u3]);

julia> Ktux,(x1,x2,x3) = polynomial_ring(Ktu,[:x1,:x2,:x3]);

julia> f1Tilde = t + 2*x1 + 2*x1^2;

julia> h = initial_zero(f1Tilde)
{a1: 2.00000}*x1^2 + {a1: 2.00000}*x1

julia> typeof(h)
AbstractAlgebra.Generic.MPoly{AbstractAlgebra.Generic.MPoly{PuiseuxMPolyRingElem{QQBarFieldElem}}}

julia> h = OscarZerodimensionalTropicalization.convert_for_roots_in_puiseux_expansion(h)
{a1: 2.00000}*x1^2 + {a1: 2.00000}*x1

julia> typeof(h)
AbstractAlgebra.Generic.Poly{QQBarFieldElem}

```
"""
function convert_for_roots_in_puiseux_expansion(h::MPolyRingElem{<:MPolyRingElem{<:PuiseuxMPolyRingElem}})
    Ktux = parent(h)
    K = coefficient_ring(base_ring(base_ring(Ktux)))
    i = findfirst(!iszero, first(exponents(h)))
    Kx, (x) = polynomial_ring(K,symbols(Ktux)[i])
    newPoly = zero(Kx)
    for (xExp, xCoeff) in zip(exponents(h), coefficients(h))
        for (uExp, uCoeff) in zip(exponents(xCoeff), coefficients(xCoeff))
            @assert iszero(uExp) "unexpected non-constant coefficient in root calculation conversion"
            @assert length(uCoeff)==1 "unexpected non-constant coefficient in root calculation conversion"
            newPoly += first(coefficients(uCoeff))*x^xExp[i]
        end
    end
    return newPoly
end



@doc raw"""
    puiseux_expansion(fiTilde::MPolyRingElem{<:MPolyRingElem{<:PuiseuxMPolyRingElem}}, w::QQFieldElem, relPrecMax::QQFieldElem)

Compute the roots of `fiTilde` of valuation `w` using Puiseux expansion.
Returned roots have relative precision that is either the maximal possible or
`relPrecMax`, whichever is smaller.

# Examples
```jldoctest
julia> K,(t,) = puiseux_polynomial_ring(algebraic_closure(QQ),["t"]);

julia> Ku,u = polynomial_ring(K, "u"=>1:2);

julia> Kux,x = polynomial_ring(Ku,2);

julia> f1 = (x[1]^2+sum([t^i for i in 0:9]));

julia> C = OscarZerodimensionalTropicalization.puiseux_expansion(f1, QQ(0), QQ(7))
2-element Vector{AbstractAlgebra.Generic.MPoly{PuiseuxMPolyRingElem{QQBarFieldElem}}}:
 t^8*u[1] + {a2: 0.209473*im}*t^7 + {a2: 0.225586*im}*t^6 + {a2: 0.246094*im}*t^5 + {a2: 0.273438*im}*t^4 + {a2: 0.312500*im}*t^3 + {a2: 0.375000*im}*t^2 + {a2: 0.500000*im}*t + {a2: 1.00000*im}
 t^8*u[1] + {a2: -0.209473*im}*t^7 + {a2: -0.225586*im}*t^6 + {a2: -0.246094*im}*t^5 + {a2: -0.273438*im}*t^4 + {a2: -0.312500*im}*t^3 + {a2: -0.375000*im}*t^2 + {a2: -0.500000*im}*t + {a2: -1.00000*im}

julia> C[1]^2+sum([t^i for i in 0:99]) # this should be above t^7
t^16*u[1]^2 + ({a2: 0.418945*im}*t^15 + {a2: 0.451172*im}*t^14 + {a2: 0.492188*im}*t^13 + {a2: 0.546875*im}*t^12 + {a2: 0.625000*im}*t^11 + {a2: 0.750000*im}*t^10 + {a2: 1.00000*im}*t^9 + {a2: 2.00000*im}*t^8)*u[1] + t^99 + t^98 + t^97 + t^96 + t^95 + t^94 + t^93 + t^92 + t^91 + t^90 + t^89 + t^88 + t^87 + t^86 + t^85 + t^84 + t^83 + t^82 + t^81 + t^80 + t^79 + t^78 + t^77 + t^76 + t^75 + t^74 + t^73 + t^72 + t^71 + t^70 + t^69 + t^68 + t^67 + t^66 + t^65 + t^64 + t^63 + t^62 + t^61 + t^60 + t^59 + t^58 + t^57 + t^56 + t^55 + t^54 + t^53 + t^52 + t^51 + t^50 + t^49 + t^48 + t^47 + t^46 + t^45 + t^44 + t^43 + t^42 + t^41 + t^40 + t^39 + t^38 + t^37 + t^36 + t^35 + t^34 + t^33 + t^32 + t^31 + t^30 + t^29 + t^28 + t^27 + t^26 + t^25 + t^24 + t^23 + t^22 + t^21 + t^20 + t^19 + t^18 + t^17 + t^16 + t^15 + {a1: 0.956121}*t^14 + {a1: 0.905492}*t^13 + {a1: 0.846011}*t^12 + {a1: 0.774414}*t^11 + {a1: 0.685150}*t^10 + {a1: 0.567322}*t^9 + {a1: 0.392761}*t^8

julia> C[2]^2+sum([t^i for i in 0:99]) # this should be above t^7
t^16*u[1]^2 + ({a2: -0.418945*im}*t^15 + {a2: -0.451172*im}*t^14 + {a2: -0.492188*im}*t^13 + {a2: -0.546875*im}*t^12 + {a2: -0.625000*im}*t^11 + {a2: -0.750000*im}*t^10 + {a2: -1.00000*im}*t^9 + {a2: -2.00000*im}*t^8)*u[1] + t^99 + t^98 + t^97 + t^96 + t^95 + t^94 + t^93 + t^92 + t^91 + t^90 + t^89 + t^88 + t^87 + t^86 + t^85 + t^84 + t^83 + t^82 + t^81 + t^80 + t^79 + t^78 + t^77 + t^76 + t^75 + t^74 + t^73 + t^72 + t^71 + t^70 + t^69 + t^68 + t^67 + t^66 + t^65 + t^64 + t^63 + t^62 + t^61 + t^60 + t^59 + t^58 + t^57 + t^56 + t^55 + t^54 + t^53 + t^52 + t^51 + t^50 + t^49 + t^48 + t^47 + t^46 + t^45 + t^44 + t^43 + t^42 + t^41 + t^40 + t^39 + t^38 + t^37 + t^36 + t^35 + t^34 + t^33 + t^32 + t^31 + t^30 + t^29 + t^28 + t^27 + t^26 + t^25 + t^24 + t^23 + t^22 + t^21 + t^20 + t^19 + t^18 + t^17 + t^16 + t^15 + {a1: 0.956121}*t^14 + {a1: 0.905492}*t^13 + {a1: 0.846011}*t^12 + {a1: 0.774414}*t^11 + {a1: 0.685150}*t^10 + {a1: 0.567322}*t^9 + {a1: 0.392761}*t^8

```
"""
function puiseux_expansion(fiTilde::MPolyRingElem{<:MPolyRingElem{<:PuiseuxMPolyRingElem}}, w::QQFieldElem, relPrecMax::QQFieldElem)
    @req length(fiTilde)>1 "polynomial must not be monomial"

    w = Rational{Int}(w) # workaround for
    
    Ktux = parent(fiTilde)
    Ktu = base_ring(Ktux)
    Kt = base_ring(Ktu)

    n = ngens(Ktux)
    i = findfirst(!iszero,first(exponents(fiTilde)))
    xi = gens(Ktux)[i]
    ui = gens(Ktu)[i]
    t = first(gens(Kt))

    if relPrecMax < 0 # maximum precision reached
        return [ui*t^w]
    end

    h = initial_zero(evaluate(fiTilde, vcat(zeros(Ktux, i-1), xi*t^w, zeros(Ktux, n-i))))
    global _debug_h = h # BUG: h is still defined over puiseux polynomial ring
    if has_non_constant_coefficients(h) # maximum possible precision reached
        return [ui*t^w]
    end

    h = convert_for_roots_in_puiseux_expansion(h)
    newRoots = elem_type(Ktu)[]
    for c in roots(h)
        if iszero(c)
            # skip zero roots, they lead to roots of valuation > w
            continue
        end
        @vprintln :PuiseuxExpansion "Found root c=$(c) at exponent w=$(w)"

        g = evaluate(fiTilde, vcat(zeros(Ktux, i-1), xi+Ktux(c)*t^w, zeros(Ktux, ngens(Ktux)-i)))

        # check whether next term exists or whether root is completely computed
        if iszero(evaluate(g, zeros(Ktux, ngens(Ktux))))
            push!(newRoots, Ktu(Kt(c)*t^w))
            continue
        end

        # compute the next term
        canComputeNextTerm, sigma = is_newton_polygon_well_defined_with_polygon(g)
        if !canComputeNextTerm # g has insufficient precision
            return [ui*t^w]
        end
        if dim(sigma) == 1 # g has only root 0
            return [zero(Ktu)]
        end

        nextExponents = [ v[1]/v[2] for v in normal_vector.(facets(sigma)) if v[2]<0 && v[1]/v[2]>w]
        for nextExponent in nextExponents
            @vprintln :PuiseuxExpansion "  Enter recursion for exponent $(nextExponent) and precision $(relPrecMax - (w - nextExponent))"
            for tailTerm in puiseux_expansion(g,nextExponent,relPrecMax - (nextExponent-w))
                push!(newRoots, Kt(c)*t^w + tailTerm)
            end
        end
    end
    return newRoots
end
