
module RC5
using Blocks, Solve, Tasks

const P8 = 0xb7
const Q8 = 0x9e
const P16 = 0xb7e1
const Q16 = 0x9e37
const P32 = 0xb7e15163
const Q32 = 0x9e3779b9
const P64 = 0xb7e151628aed2a6b
const Q64 = 0x9e3779b97f4a7c15

immutable State{W<:Unsigned}
    r::Uint8
    k::Array{Uint8}
    s::Array{W}
    rotate::Bool
end

State(w::Type{Uint8}, r::Uint8, k::Array{Uint8}; rotate=true) = 
State{w}(r, k, expand(w, r, k, P8, Q8), rotate)

State(w::Type{Uint16}, r::Uint8, k::Array{Uint8}; rotate=true) = 
State{w}(r, k, expand(w, r, k, P16, Q16), rotate)

State(w::Type{Uint32}, r::Uint8, k::Array{Uint8}; rotate=true) = 
State{w}(r, k, expand(w, r, k, P32, Q32), rotate)

State(w::Type{Uint64}, r::Uint8, k::Array{Uint8}; rotate=true) = 
State{w}(r, k, expand(w, r, k, P64, Q64), rotate)

function pad{W<:Unsigned}(n::W)
    s = @sprintf("%x", n)
    while length(s) < sizeof(W)
        s = "0" + s
    end
    s
end

sprintf_state{W<:Unsigned}(s::State{W}) = join(map(pad, s.s), " ")

function Base.show{W<:Unsigned}(io::IO, s::State{W})
#    print(io, @sprintf("RC5-%d/%d/%d 0x%s", 
#                       8*sizeof(W), s.r, length(s.k), bytes2hex(s.k)))
    print(io, @sprintf("RC5-%d/%d/%d 0x%s\n%s\n", 
                       8*sizeof(W), s.r, length(s.k), bytes2hex(s.k),
                       sprintf_state(s)))
end

function same_state{W<:Unsigned}(s1::State{W}, s2::State{W})
    s1.r == s2.r && s1.s == s2.s && s1.rotate == s2.rotate
end

function rotatel{W<:Unsigned}(x::W, n::Unsigned)
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
        s[i+1] = rotatel(w, s[i+1] + (a + b), 0x3)
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
    @printf("a = a + s[1] = %x\n", a)
    b::W = b + s.s[2]
    @printf("b = b + s[2] = %x\n", b)
    for i = 1:s.r
        @printf("round %d\n", i)
        a = a $ b
        @printf("a = a \$ b = %x\n", a)
        if s.rotate
            a = rotatel(W, a, b)
            @printf("a = a <<< b = %x\n", a)
        end
        a = a + s.s[2i+1]
        @printf("a = a + s[%d] = %x\n", 2i+1, a)
        b = b $ a
        @printf("b = b \$ a = %x\n", b)
        if s.rotate
            b = rotatel(W, b, a)
            @printf("b = b <<< a = %x\n", b)
        end
        b = b + s.s[2i+2]
        @printf("b = b + s[%d] = %x\n", 2i+2, b)
    end
    a, b
end

function encrypt{W<:Unsigned}(s::State{W}, plain)
    e = Task() do
        a = nothing
        for b in pack(Uint32, plain)
            if a == nothing
                a = b
            else
                c, d = encrypt(s, a, b)
                @printf("%x %x -> %x %x\n", a, b, c, d)
                produce(c)
                produce(d)
                a = nothing
            end
        end
    end
    unpack(Uint32, e)
end


function make_solve_r0{W<:Unsigned}(::Type{W}, k)
    w = sizeof(W)
    function solve(e)
        a, b = pack(W, e(take(2*w, constant(0x0))))
        s = State(W, 0x0, collect(Uint8, take(k, constant(0x0))))
        s.s[1] = a
        s.s[2] = b
        s
    end
end

function make_solve_r1_noro{W<:Unsigned}(::Type{W}, k)
    function solve(e)
        # a' = ((a + s[1]) $ (b + s[2])) + s[3]
        # a0'-a1' = ((a0 + s[1]) $ (b0 + s[2])) - ((a1 + s[1]) $ (b1 + s[2]))
        # choose b0 == b1
        # a0'-a1' = ((a0 + s[1]) $ (b + s[2])) - ((a1 + s[1]) $ (b + s[2]))
        #         = ((a0 + c) $ K) - ((a1 + c) $ K)
        # choose a0 and a1 to be same except for 1 bit - can get bit for K
        # except for msb; see Experiment.jl
        k::W = 0x0
        m::W = 0x1
        for b = 0:(8*sizeof(W)-1)
            while true:
                a0::W = rand(W)
                a1::W = a0 + m
                ap0, _, ap1, _ = e(W[a0, 0x0, a1, 0x0])
                d = ap0 - ap1
                if d == m
                    k = k + m
                    break
                elseif d == -m
                    break
                end
            end
            m = m << 1
        end
        # at this point we know k (s[2]) except for msb (m)
        for s2 in (k, k+m)
            # if we know s[2], set b0+s[2]=0, b1+s[2]=0xf..f, a0=0, a1=-1
            # a0'-a1' = ((a0+s[1]) $ (b0+s[2])) - ((a1+s[1]) $ (b1+s[2]))
            #         = (s[1] - ((s[1]-1) $ 0xf..f))
            #         = s[1] - (-s[1])
            ap0, _, ap1, _ = e(W[0x0, -s2, -1, -1])
            s1 = (ap0 - ap1) >> 1
            s3 = # TODO
            # check if the current k is correct
            
        end
    end
end


make_keygen(w, r, k; rotate=true) = 
() -> State(w, r, collect(Uint8, take(k, rands(Uint8))), rotate=rotate)

function solutions()
    solve_known_cipher(3, make_solve_r0(Uint32, 0x2), 
                       make_keygen(Uint32, 0x0, 0x2),
                       encrypt, eq=same_state)
    solve_known_cipher(3, make_solve_r1_noro(Uint32, 0x2), 
                       make_keygen(Uint32, 0x1, 0x2, rotate=false),
                       encrypt, eq=same_state)
end


function test_rotatel()
    y = rotatel(0x81, 0x1)
    @assert y == 0x03 y
    y = rotatel(0x81, 0x9)
    @assert y == 0x03 y
    y = rotatel(0x81, 0x81)
    @assert y == 0x03 y
end

function test_vectors()
    a, b = encrypt(State(Uint32, 0x0c, zeros(Uint8, 16)), 
                   0x00000000, 0x00000000)
    @assert a == 0xeedba521 a
    @assert b == 0x6d8f4b15 b
    # note that bytes are packed little-endian, while the rc5 paper shows
    # 32bit integers for the half-blocks.
    c = collect(Uint8, 
                encrypt(State(Uint32, 0x0c, 
                              hex2bytes("00000000000000000000000000000000")),
                        hex2bytes("0000000000000000")))
    @assert c == hex2bytes("21a5dbee154b8f6d")
    c = collect(Uint8, 
                encrypt(State(Uint32, 0x0c, 
                              hex2bytes("5269f149d41ba0152497574d7f153125")),
                        hex2bytes("65c178b284d197cc")))
    @assert c == hex2bytes("eb44e415da319824")
end

function tests()
    test_rotatel()
    test_vectors()
end

tests()
solutions()

end
