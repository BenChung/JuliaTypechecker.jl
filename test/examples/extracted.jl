
module Math

@assume_effects :consistent @inline function two_mul(x::Float16, y::Float16)
    if Core.Intrinsics.have_fma(Float16)
        xy = x*y
        return xy, fma(x, y, -xy)
    end
    xy = widen(x)*y
    Txy = Float16(xy)
    return Txy, Float16(xy-Txy)
end

function ^(x::Float32, n::Int)
    n == -2 && return (i=inv(x); i*i)
    n == 3 && return x*x*x #keep compatibility with literal_pow
    n < 0 && return Float32(Base.power_by_squaring(inv(Float64(x)),-n))
    Float32(Base.power_by_squaring(Float64(x),n))
end

function _evalpoly(z::Complex{Float64}, p::Vector{Float64})
    length(p) == 1 && return p[1]
    N = length(p)
    a = p[end]
    b = p[end-1]

    x = real(z)
    y = imag(z)
    r = 2x
    s = muladd(x, x, y*y)
    for i in N-2:-1:1
        ai = a
        a = muladd(r, ai, b)
        b = muladd(-s, ai, p[i])
    end
    ai = a
    muladd(ai, z, b)
end

rad2deg(z::Float64) = (z/pi)*180

@inline function pow_body(x::Float32, y::Float32)
    return Float32(exp2(log2(abs(widen(x))) * y))
end

function _hypot(x::Float64, y::Float64)
    # preserves unit
    axu = abs(x)
    ayu = abs(y)

    # unitless
    ax = axu / oneunit(axu)
    ay = ayu / oneunit(ayu)

    # Return Inf if either or both inputs is Inf (Compliance with IEEE754)
    if isinf(ax) || isinf(ay)
        return typeof(axu)(Inf)
    end

    # Order the operands
    if ay > ax
        axu, ayu = ayu, axu
        ax, ay = ay, ax
    end

    # Widely varying operands
    if ay <= ax*sqrt(eps(typeof(ax))/2)  #Note: This also gets ay == 0
        return axu
    end

    # Operands do not vary widely
    scale = eps(typeof(ax))*sqrt(floatmin(ax))  #Rescaling constant
    if ax > sqrt(floatmax(ax)/2)
        ax = ax*scale
        ay = ay*scale
        scale = inv(scale)
    elseif ay < sqrt(floatmin(ax))
        ax = ax/scale
        ay = ay/scale
    else
        scale = oneunit(scale)
    end
    h = sqrt(muladd(ax, ax, ay*ay))
    # This branch is correctly rounded but requires a native hardware fma.
    if Core.Intrinsics.have_fma(typeof(h))
        hsquared = h*h
        axsquared = ax*ax
        h -= (fma(-ay, ay, hsquared-axsquared) + fma(h, h,-hsquared) - fma(ax, ax, -axsquared))/(2*h)
    # This branch is within one ulp of correctly rounded.
    else
        if h <= 2*ay
            delta = h-ay
            h -= muladd(delta, delta-2*(ax-ay), ax*(2*delta - ax))/(2*h)
        else
            delta = h-ax
            h -= muladd(delta, delta, muladd(ay, (4*delta - ay), 2*delta*(ax - 2*ay)))/(2*h)
        end
    end
    return h*scale*oneunit(axu)
end
atan(y::Float64, x::Float64) = atan(promote(float(y),float(x))...)

function rem(x::Float64, p::Float64, ::RoundingMode)
    (iszero(p) || !isfinite(x) || isnan(p)) && return Float64(NaN)
    x == p && return copysign(zero(Float64), x)
    oldx = x
    x = abs(rem(x, 2p))  # 2p may overflow but that's okay
    p = abs(p)
    if p < 2 * floatmin(Float64)  # Check whether dividing p by 2 will underflow
        if 2x > p
            x -= p
            if 2x >= p
                x -= p
            end
        end
    else
        p_half = p / 2
        if x > p_half
            x -= p
            if x >= p_half
                x -= p
            end
        end
    end
    return flipsign(x, oldx)
end

@constprop :aggressive @inline function ^(x::Float64, n::Int64)
    n == 0 && return one(x)
    return pow_body(x, n)
end

function rem2pi(x::Float64, ::RoundingMode)
    isfinite(x) || return NaN

    ax = abs(x)
    ax <= 2*Float64(pi,RoundDown) && return x

    n,y = rem_pio2_kernel(ax)
    z = 0.0
    if iseven(n)
        if n & 2 == 2 # n % 4 == 2: add pi
            z = add22condh(y.hi,y.lo,pi2o2_h,pi2o2_l)
        else          # n % 4 == 0: add 0 or 2pi
            if y.hi > 0
                z = y.hi+y.lo
            else      # negative: add 2pi
                z = add22condh(y.hi,y.lo,pi4o2_h,pi4o2_l)
            end
        end
    else
        if n & 2 == 2 # n % 4 == 3: add 3pi/2
            z = add22condh(y.hi,y.lo,pi3o2_h,pi3o2_l)
        else          # n % 4 == 1: add pi/2
            z = add22condh(y.hi,y.lo,pi1o2_h,pi1o2_l)
        end
    end
    copysign(z,x)
end


end