module FixedPoint

export AbstractFixed
abstract type AbstractFixed{f, T <: Signed} <: Real end

export Fixed
struct Internal end
struct Fixed{f, T <: Signed} <: AbstractFixed{f, T}
    m::T
    function Fixed{f, T}(::Internal, m::T) where {f, T <: Signed}
        # We could handle this, but would need to special-case range
        # calculations size "sizeof" doesn't work then
        @assert T !== BigInt
        @assert typeof(f) <: Integer
        # Ensure +1 can be represented
        @assert f >= 0 && f < 8*sizeof(T)-1
        new{f, T}(m)
    end
end

Fixed{f}(::Internal, m::T) where {f, T <: Signed} = Fixed{f, T}(Internal(), m)



Base.eltype(::Type{Fixed{f, T}}) where {f, T} = T
Base.eltype(::Fixed{f, T}) where {f, T} = T
Base.precision(::Type{Fixed{f, T}}) where {f, T} = f
Base.precision(::Fixed{f}) where {f} = f

Base.numerator(x::Fixed{f, T}) where {f, T} = x.m
Base.denominator(x::Fixed{f, T}) where {f, T} = T(1) << Unsigned(f)



# Trivial conversion
function Fixed{f, T}(x::Fixed{f, T}) where {f, T <: Signed}
    x
end

# Convert between different representation types (with same number of
# fraction bits)
function Fixed{f, T}(x::Fixed{f, U}) where {f, T <: Signed, U <: Signed}
    # Note: if we convert to a smaller type, then we need to check for
    # overflow. Luckily, Julia does this automatically, so we don't
    # need to handle this.
    Fixed{f, T}(Internal(), T(x.m))
end

# Convert between different numbers of fraction bits (with same
# representation type)
function Fixed{f, T}(x::Fixed{g, T}) where {f, g, T <: Signed}
    s = Signed(f) - Signed(g)
    if s >= 0
        # No rounding necessary, just shift
        # Check for overflow
        @assert x.m >> (Unsigned(8*sizeof(T)) - Unsigned(s)) == -T(signbit(x.m))
        Fixed{f, T}(Internal(), x.m << Unsigned(s))
    else
        # Round by adding and offset before shifting

        Fg = Fixed{g, T}
        z = Fg(Internal(), T(0))
        e = Fg(Internal(), T(1))
        h = Fg(Internal(), T(1) << Unsigned(-s-1))
        o = Fg(Internal(), T(1) << Unsigned(-s))

        # Round towards -infinity
        offset_floor = z
        # Round towards +infinity
        offset_ceil = o - e
        # Break ties towards -infinity
        offset_down = h - e
        # Break ties towards +infinity
        offset_up = h
        # Break ties towards the next even number
        offset_even = h - e + Fg(Internal(), (x.m >> Unsigned(-s)) & T(1))

        y = x + offset_even
        Fixed{f, T}(Internal(), y.m >> Unsigned(-s))
    end
end

function Fixed{f}(x::Fixed{g, T}) where {f, g, T <: Signed}
    Fixed{f, T}(x)
end

# General conversion
function Fixed{f, T}(x::Fixed{g, U}) where {f, g, T <: Signed, U <: Signed}
    if sizeof(T) <= sizeof(U)
        # shift first, convert later
        Fixed{f, T}(Fixed{f, U}(x))
    else
        # convert first, shift later
        Fixed{f, T}(Fixed{g, T}(x))
    end
end

# Create from an integer
function Fixed(x::T) where {T <: Signed}
    Fixed{0, T}(Internal(), x)
end
function Fixed{f, T}(x::Integer) where {f, T <: Signed}
    Fixed{f, T}(Fixed(x))
end
function Fixed{f, T}(x::BigInt) where {f, T <: Signed}
    Fixed{f, T}(Int128(x))
end

# Create from a rational
function Fixed{f, T}(x::Rational{I}) where {f, T <: Signed, I <: Signed}
    U = promote_type(T, I)
    Fixed{f, T}(Fixed{f, U}(numerator(x)) / Fixed{f, U}(denominator(x)))
end
function Fixed{f, T}(x::Rational{BigInt}) where {f, T <: Signed}
    Fixed{f, T}(Rational{Int64}(x))
end

# Create from a floating point number
function Fixed{f, T}(x::AbstractFloat) where {f, T <: Signed}
    Fixed{f, T}(Internal(), round(T, ldexp(x, Unsigned(f))))
end

# Convert to a rational number
function (::Type{R})(x::Fixed{f, T})::R where {f, T <: Signed, R <: Rational}
    # This uses the precison of T to normalize the result, which might
    # not be sufficient
    # R(x.m,  T(1) << Unsigned(f))
    R(x.m) // (T(1) << Unsigned(f))
end

# Convert to a floating-point number
function Base.float(::Type{Fixed{f, T}})::Type where {f, T}
    # f <= 11 && return Float16
    # f <= 24 && return Float32
    f <= 53 && return Float64
    BigFloat
end

function (::Type{F})(x::Fixed{f, T})::F where
        {f, T <: Signed, F <: AbstractFloat}
    ldexp(F(x.m), -Signed(f))
end



# Functions without value arguments

function Base.zero(::Type{Fixed{f, T}})::Fixed{f, T} where {f, T}
    Fixed{f, T}(Internal(), T(0))
end

function Base.one(::Type{Fixed{f, T}})::Fixed{f, T} where {f, T}
    Fixed{f, T}(Internal(), T(1) << Unsigned(f))
end

function Base.eps(::Type{Fixed{f, T}})::Fixed{f, T} where {f, T}
    Fixed{f, T}(Internal(), T(1))
end

function Base.typemin(::Type{Fixed{f, T}})::Fixed{f, T} where {f, T}
    # Claim a symmetric range
    Fixed{f, T}(Internal(), -typemax(T))
end

function Base.typemax(::Type{Fixed{f, T}})::Fixed{f, T} where {f, T}
    Fixed{f, T}(Internal(), typemax(T))
end



# Unary functions

function Base. +(x::Fixed{f, T})::Fixed{f, T} where {f, T}
    Fixed{f, T}(Internal(), + x.m)
end

function Base. -(x::Fixed{f, T})::Fixed{f, T} where {f, T}
    Fixed{f, T}(Internal(), - x.m)
end

function Base. *(x::Fixed{f, T})::Fixed{f, T} where {f, T}
    Fixed{f, T}(Internal(), *(x.m))
end

function Base. ^(x::Fixed{f, T}, a::Unsigned)::Fixed{f, T} where {f, T}
    r = one(x)
    if isodd(a)
        r = x
    end
    a >>= 1
    while a > 0
        x *= x
        if isodd(a)
            r *= x
        end
        a >>= 1
    end
    r
end

function Base. ^(x::Fixed{f, T}, a::Signed)::Fixed{f, T} where {f, T}
    if a >= 0
        x ^ Unsigned(a)
    else
        inv(x ^ Unsigned(-a))
    end
end

function Base.abs(x::Fixed{f, T})::Fixed{f, T} where {f, T}
    Fixed{f, T}(Internal(), abs(x.m))
end

function Base.hash(x::Fixed{f, T}, h::UInt)::UInt where {f, T}
    hash(hash(x.m, h), 0xd8bf79c19fa81795 % UInt)
end

function Base.inv(x::Fixed{f, T})::Fixed{f, T} where {f, T}
    # This is not very accurate
    # one(x) / x
    T1 = widen(T)
    f1 = 8 * sizeof(T1) - 2
    o = T1(1) << Unsigned(f1)
    # TODO: (see also Base./ below)
    # - round correctly
    # Use modulus for this?
    # d, m = fldmod(o, x.m)
    d = fld(o, x.m)
    Fixed{f, T}(Fixed{typeof(f)(f1 - f)}(Internal(), d))
end

function Base.sign(x::Fixed{f, T})::Fixed{f, T} where {f, T}
    Fixed{f, T}(sign(x.m))
end

function Base.signbit(x::Fixed{f, T})::Bool where {f, T}
    signbit(x.m)
end

function Base.widen(::Type{Fixed{f, T}})::Type where {f, T}
    @assert widen(T) !== BigInt
    Fixed{typeof(f)(2*f), widen(T)}
end
function Base.widen(x::Fixed{f, T}) where {f, T}
    Fixed{typeof(f)(2*f)}(Fixed{f}(Internal(), widen(x.m)))
end

# Widen, but extend only the range and not the precision
export widenRange
function widenRange(::Type{Fixed{f, T}})::Type where {f, T}
    @assert widen(T) !== BigInt
    T1 = widen(T)
    Fixed{f, T}
end
function widenRange(x::Fixed{f, T}) where {f, T}
    Fixed{f}(Internal(), widen(x.m))
end

# Widen, but extend only the precision and not the range
export widenPrecision
function widenPrecision(::Type{Fixed{f, T}})::Type where {f, T}
    @assert widen(T) !== BigInt
    T1 = widen(T)
    f1 = typeof(f)(f + 8 * (sizeof(T1) - sizeof(T)))
    @assert f1 >= f
    Fixed{f1, T1}
end
function widenPrecision(x::Fixed{f, T}) where {f, T}
    x1 = widenRange(x)
    f1 = typeof(f)(f + 8 * (sizeof(x1) - sizeof(x)))
    @assert f1 >= f
    Fixed{f1}(x1)
end



# Binary functions

function Base. +(x::Fixed{f, T}, y::Fixed{f, T})::Fixed{f, T} where {f, T}
    Fixed{f, T}(Internal(), x.m + y.m)
end

function Base. -(x::Fixed{f, T}, y::Fixed{f, T})::Fixed{f, T} where {f, T}
    Fixed{f, T}(Internal(), x.m - y.m)
end

function Base.widemul(x::Fixed{f, T}, y::Fixed{f, T}) where {f, T}
    Fixed{typeof(f)(2*f)}(Internal(), widemul(x.m, y.m))
end

function Base. *(x::Fixed{f, T}, y::Fixed{f, T})::Fixed{f, T} where {f, T}
    Fixed{f, T}(widemul(x, y))
end

function Base. /(x::Fixed{f, T}, y::Fixed{f, T})::Fixed{f, T} where {f, T}
    # x1 = widenPrecision(x)
    x1 = widen(x)
    f1 = precision(x1)
    @assert f1 - f >= f
    # TODO: (see also Base.inv above)
    # - prevent overflow while adding
    # - break ties correctly when rounding
    # Use modulus for this?
    d, m = fldmod(x1.m, y.m)
    d0 = d
    if y.m >= 0
        if m << 1 > y.m
            # Round up
            d += T(1)
        elseif m << 1 == y.m
            # Round up if the result is odd
            d += d & T(1)
        end
    else
        if m << 1 < y.m
            # Round up
            d += T(1)
        elseif m << 1 == y.m
            # Round up if the result is odd
            if d & T(1) != 0
                d += T(1)
            end
        end
    end
    # Avoid double rounding
    @assert f1 - f == f
    Fixed{f, T}(Fixed{typeof(f)(f1 - f)}(Internal(), d))
end

function Base. \(x::Fixed{f, T}, y::Fixed{f, T})::Fixed{f, T} where {f, T}
    y / x
end

function Base. ==(x::Fixed{f, T}, y::Fixed{f, T})::Bool where {f, T}
    x.m == y.m
end

function Base. !=(x::Fixed{f, T}, y::Fixed{f, T})::Bool where {f, T}
    x.m != y.m
end

function Base. <(x::Fixed{f, T}, y::Fixed{f, T})::Bool where {f, T}
    x.m < y.m
end

function Base. <=(x::Fixed{f, T}, y::Fixed{f, T})::Bool where {f, T}
    x.m <= y.m
end

function Base. >(x::Fixed{f, T}, y::Fixed{f, T})::Bool where {f, T}
    x.m > y.m
end

function Base. >=(x::Fixed{f, T}, y::Fixed{f, T})::Bool where {f, T}
    x.m >= y.m
end

function Base.isequal(x::Fixed{f, T}, y::Fixed{f, T})::Bool where {f, T}
    x == y
end

function Base.isless(x::Fixed{f, T}, y::Fixed{f, T})::Bool where {f, T}
    x < y
end

function Base.copysign(x::Fixed{f, T}, y::Fixed{f, T})::Fixed{f, T} where {f, T}
    Fixed{f, T}(Internal(), copysign(x.m, y.m))
end

function Base.max(x::Fixed{f, T}, y::Fixed{f, T})::Fixed{f, T} where {f, T}
    Fixed{f, T}(Internal(), max(x.m, y.m))
end

function Base.min(x::Fixed{f, T}, y::Fixed{f, T})::Fixed{f, T} where {f, T}
    Fixed{f, T}(Internal(), min(x.m, y.m))
end



# Ternary functions

function Base.fma(x::Fixed{f, T},
                  y::Fixed{f, T},
                  z::Fixed{f, T})::Fixed{f, T} where {f, T}
    r = widemul(x, y)
    Fixed{f, T}(r + Fixed{precision(r), eltype(r)}(z))
end

function Base.muladd(x::Fixed{f, T},
                     y::Fixed{f, T},
                     z::Fixed{f, T})::Fixed{f, T} where {f, T}
    x * y + z
end



# Elementary functions

function Base.sqrt(x::Fixed{f, T})::Fixed{f, T} where {f, T}
    @assert x >= zero(x)
    # Special case
    if x == zero(x)
        return zero(x)
    end
    # Initial approximation
    r = Fixed{f, T}(sqrt(Float64(x)))
    # Iteration
    half = Fixed{f, T}(1//2)
    b = 52                      # Float64 has 53 accurate bits
    while b < f
        r = half * (r + x / r)
        b *= 2                  # Each iteration doubles the accurate bits
    end
    r
end

end
