using Test
using FixedPoint



const R = Rational{BigInt}
const R1 = Rational{Int64}



# Exhaustive tests for Int8, just because we can

function nullary(::Type{F8}) where F8
    f = precision(F8)
    typemax8 = typemax(Int8) >> f
    inrange8(x) = abs(x) <= typemax8
    eps8 = R(1, 2^f)
    round8(x) = round(x * 2^f) / 2^f

    @testset "Nullary functions, $f fraction bits" begin
        @test isequal(R(zero(F8)), zero(R))
        @test isequal(R(one(F8)), one(R))
        @test isequal(R(eps(F8)), inv(R(2^f)))
        @test isequal(R(typemin(F8)), -R(typemax(F8)))
        @test isequal(R(typemax(F8)), R(typemax(Int8)) / R(2^f))
    end
end

function basic(::Type{F8}) where {F8}
    f = precision(F8)
    typemax8 = typemax(Int8) >> f
    inrange8(x) = abs(x) <= typemax8
    eps8 = R(1, 2^f)
    round8(x) = round(x * 2^f) / 2^f

    @testset "Basic properties, $f fraction bits" begin
        for i in -typemax(Int8) : typemax(Int8)
            x = F8(FixedPoint.Internal(), i)
            r = R(i, 2^f)

            @test isequal(eltype(x), Int8)
            @test isequal(precision(x), f)
            @test isequal(numerator(x), i)
            @test isequal(denominator(x), Int8(2)^f)
        end
    end
end

function conversions(::Type{F8}) where {F8}
    f = precision(F8)
    typemax8 = typemax(Int8) >> f
    inrange8(x) = abs(x) <= typemax8
    eps8 = R(1, 2^f)
    round8(x) = round(x * 2^f) / 2^f

    @testset "Type conversions, $f fraction bits" begin
        for i in -typemax(Int8) : typemax(Int8)
            x = F8(FixedPoint.Internal(), i)
            r = R(i, 2^f)

            @test isequal(F8(x), x)
            @test isequal(R(x), r)
            @test isequal(F8(r), x)
            @test isequal(R(Float32(x)), r)
            @test isequal(F8(Float32(r)), x)
            @test isequal(R(float(x)), float(r))
            @test isequal(F8(float(r)), x)
        end
    end
end

function unary(::Type{F8}) where {F8}
    f = precision(F8)
    typemax8 = typemax(Int8) >> f
    inrange8(x) = abs(x) <= typemax8
    eps8 = R(1, 2^f)
    round8(x) = round(x * 2^f) / 2^f

    @testset "Unary functions, $f fraction bits" begin
        for i in -typemax(Int8) : typemax(Int8)
            x = F8(FixedPoint.Internal(), i)
            r = R(i, 2^f)

            @test isequal(R(+x), +r)
            @test isequal(R(-x), -r)
            @test isequal(R(*(x)), *(r))
            @test isequal(R(abs(x)), abs(r))
            @test hash(x) === hash(x)
            @test hash(x) !== hash(i)
            @test hash(x) !== hash(r)
            if r != 0 && inrange8(inv(r))
                # y = inv(r)
                # dy = max(abs(r), abs(y)) * eps8
                # # TODO: Instead of allowing for an error here, fix the
                # # implementation and require things to be rounded
                # # correctly
                # if inrange8(y) && abs(y) > dy
                #     @test abs(R(inv(x)) - round8(inv(r))) <= dy
                # end
                if !isequal(R(inv(x)), round8(inv(r)))
                    @show f i x r R(inv(x)) round8(inv(r))
                end
                @test isequal(R(inv(x)), round8(inv(r)))
            end
            @test isequal(R(sign(x)), sign(r))
            for a in -10:10
                if r != 0
                    y = r^a
                    dy = 4 * max(1, abs(r), abs(y)) * eps8
                    if inrange8(y) && (a >= 0 || inrange8(inv(y))) &&
                            abs(y) > dy && (a >= 0 || abs(inv(y)) > dy)
                        @test abs(R(x^a) - y) <= dy
                    end
                end
            end
        end
    end
end

function binary(::Type{F8}) where {F8}
    f = precision(F8)
    typemax8 = typemax(Int8) >> f
    inrange8(x) = abs(x) <= typemax8
    eps8 = R(1, 2^f)
    round8(x) = round(x * 2^f) / 2^f

    @testset "Binary functions, $f fraction bits" begin
        for i in -typemax(Int8) : typemax(Int8),
                j in -typemax(Int8) : typemax(Int8)
            x = F8(FixedPoint.Internal(), i)
            y = F8(FixedPoint.Internal(), j)
            r = R(i, 2^f)
            s = R(j, 2^f)

            @test (r == s) === (hash(x) == hash(y))

            if inrange8(r + s)
                @test isequal(R(x + y), r + s)
            end
            if inrange8(r - s)
                @test isequal(R(x - y), r - s)
            end
            if inrange8(r * s)
                @test isequal(R(x * y), round8(r * s))
            end
            if s != 0 && inrange8(r / s)
                @test isequal(R(x / y), round8(r / s))
            end
            if r != 0 && inrange8(r \ s)
                @test isequal(R(x \ y), round8(r \ s))
            end
            @test isequal(R(copysign(x, y)), copysign(r, s))
            @test isequal(R(flipsign(x, y)), flipsign(r, s))
            @test isequal(R(max(x, y)), max(r, s))
            @test isequal(R(min(x, y)), min(r, s))
        end
    end
end

function comparisons(::Type{F8}) where {F8}
    f = precision(F8)
    typemax8 = typemax(Int8) >> f
    inrange8(x) = abs(x) <= typemax8
    eps8 = R(1, 2^f)
    round8(x) = round(x * 2^f) / 2^f

    @testset "Comparison operators, $f fraction bits" begin
        for i in -typemax(Int8) : typemax(Int8),
                j in -typemax(Int8) : typemax(Int8)
            x = F8(FixedPoint.Internal(), i)
            y = F8(FixedPoint.Internal(), j)
            r = R(i, 2^f)
            s = R(j, 2^f)
            @test isequal(x == y, r == s)
            @test isequal(x != y, r != s)
            @test isequal(x < y, r < s)
            @test isequal(x <= y, r <= s)
            @test isequal(x > y, r > s)
            @test isequal(x >= y, r >= s)
        end
    end
end

function ternary(::Type{F8}) where {F8}
    f = precision(F8)
    typemax8 = typemax(Int8) >> f
    inrange8(x) = abs(x) <= typemax8
    eps8 = R(1, 2^f)
    round8(x) = round(x * 2^f) / 2^f

    @testset "Ternary functions, $f fraction bits" begin
        for i in -typemax(Int8) : typemax(Int8),
                j in -typemax(Int8) : typemax(Int8),
                k in -typemax(Int8) : typemax(Int8)
            x = F8(FixedPoint.Internal(), i)
            y = F8(FixedPoint.Internal(), j)
            z = F8(FixedPoint.Internal(), k)
            r = R1(i, 2^f)
            s = R1(j, 2^f)
            t = R1(k, 2^f)
    
            if inrange8(r * s) && inrange8(muladd(r, s, t))
                q = muladd(r, s, t)
                dq = max(1, abs(r), abs(s), abs(t), abs(q)) * R1(1, 2^f)
                @test abs(R1(muladd(x, y, z)) - q) <= dq
            end
            if inrange8(r * s) && inrange8(fma(r, s, t))
                @test isequal(R1(fma(x, y, z)), round8(fma(r, s, t)))
            end
        end
    end
end

function elementary(::Type{F8}) where {F8}
    f = precision(F8)
    typemax8 = typemax(Int8) >> f
    inrange8(x) = abs(x) <= typemax8
    eps8 = R(1, 2^f)
    round8(x) = round(x * 2^f) / 2^f

    @testset "Elementary functions, $f fraction bits" begin
        for i in -typemax(Int8) : typemax(Int8)
            x = F8(FixedPoint.Internal(), i)
            r = R(i, 2^f)

            if r >= 0
                @test isequal(R(sqrt(x)), round8(sqrt(r)))
            end
        end
    end
end



for f in 0:6
    F8 = Fixed{f, Int8}
    nullary(F8)
    basic(F8)
    conversions(F8)
    unary(F8)
    binary(F8)
    comparisons(F8)
    ternary(F8)
    elementary(F8)
end
