
module Math

max(x::T, y::T) where {T<:AbstractFloat} =
	ifelse((y > x) | (signbit(y) < signbit(x)), ifelse(isnan(x), x, y), ifelse(isnan(y), y, x))
    
end