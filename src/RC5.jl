
module RC5

const P8 = 0xb7
const Q8 = 0x9e

const P16 = 0xb7e1
const Q16 = 0x9e37

const P32 = 0xb7e15163
const Q32 = 0x9e3779b9

const P64 = 0xb7e151628aed2a6b
const Q64 = 0x9e3779b97f4a7c15

immutable type State{W<:Unsigned}
    w::Type{W}
    r::Uint8
    k::Array{Uint8}
    s::Array{W}
end

function Base.show(io::IO, s::State)
    print(io, @sprintf("RC5-%d/%d/%d 0x%s", 
                       8*sizeof(s.w), s.r, length(s.k), bytes2hex(s.k)))
end

function rc5(w::Type, r::Uint8, k::Array{Uint8})
    if w == Uint8
        State{w}(w, r, k, expand(w, r, k, P8, Q8))
    elseif w == Uint16
        State{w}(w, r, k, expand(w, r, k, P16, Q16))
    elseif w == Uint32
        State{w}(w, r, k, expand(w, r, k, P32, Q32))
    elseif w == Uint64
        State{w}(w, r, k, expand(w, r, k, P64, Q64))
    else
        throw(DomainError())
    end
end

function rotatel{W<:Unsigned}(x::W, n::Integer)
    w = 8 * sizeof(W)
    m = n % w
    convert(W, (x << m) | (x >>> (w - m)))
end
rotatel{W<:Unsigned}(::Type{W}, x::Integer, n::Integer) = 
    rotatel(convert(W, x), n)

function expand{W<:Unsigned}(w::Type{W}, r::Uint8, k::Array{Uint8}, p::W, q::W)
    u = sizeof(w)
    b = length(k)
    c::Uint8 = ceil(b / u)
    l = zeros(w, c)
    for i = (b-1):-1:0
        l[div(i, u)+1] = (l[div(i, u)+1] << 8) + k[i+1]
    end
    t = 2(r+1)
    s = zeros(w, t)
    s[1] = p
    for i = 2:t
        s[i] = s[i-1] + q
    end
    i = j = 0
    a::W, b::W = 0x0, 0x0
    for _ = 1:3*max(t, c)
        s[i+1] = rotatel(w, s[i+1] + (a + b), 3)
        a = s[i+1]
        l[j+1] = rotatel(w, l[j+1] + (a + b), a + b)
        b = l[j+1]
        i = (i+1) % t
        j = (j+1) % c
    end
    s
end

function encrypt{W<:Unsigned}(s::State{W}, a::W, b::W)
    a::W = a + s.s[1]
    b::W = b + s.s[2]
    for i = 1:s.r
        a = rotatel(s.w, a $ b, b) + s.s[2i+1]
        b = rotatel(s.w, a $ b, a) + s.s[2i+2]
    end
    a, b
end


function test_rotatel()
    y = rotatel(0x81, 1)
    @assert y == 0x03 y
    y = rotatel(0x81, 9)
    @assert y == 0x03 y
    y = rotatel(0x81, 0x81)
    @assert y == 0x03 y
end

function test_vectors()
    a, b = encrypt(rc5(Uint32, 0x0c, zeros(Uint8, 16)), 0x00000000, 0x00000000)
    @assert a == 0xeedba521 a
    @assert b == 0x6d8f4b15 b
end

function tests()
    test_rotatel()
    test_vectors()
end

end

RC5.tests()
println(RC5.rc5(Uint8, 0x0c, b"secret"))
println(RC5.rc5(Uint32, 0x0c, b"1234567812345678"))
