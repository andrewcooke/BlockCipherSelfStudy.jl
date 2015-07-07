
module RC5

using Compat: @compat

using ..Blocks: unpack, group, pack, chain, pad, produce_from
using ..Tasks: take, constant
using ..Solve: rands, same_ctext, key_from_encrypt, same_ptext,
               ptext_from_encrypt

export tests, solutions

# RC5 (with and without rotation, but no decryption, currently) and an
# implementation of the following attacks:
#
# - derivation of internal state using adaptive plaintext for 0 rounds
#   and no rotation
# - same for 1 round and no rotation
# - decryption of least significant bits of half-block, via dictionary,
#   for any number of rounds with no rotation
# - decryption using adaptive plaintext for any number of rounds with
#   no rotation


# ---- RC5 cipher support (state, encryption, etc)

# the key is expanded to give a (immutable) State instance, which is used 
# for encryption.  note that everything is parameterised by half-block 
# size, as well as key (length), state size, and rotation (disabling
# rotation is not part of the official RC5 definition, but is used here
# to reduce strength).

const P8 = 0xb7
const Q8 = 0x9e
const P16 = 0xb7e1
const Q16 = 0x9e37
const P32 = 0xb7e15163
const Q32 = 0x9e3779b9
const P64 = 0xb7e151628aed2a6b
const Q64 = 0x9e3779b97f4a7c15

abstract Rotation
type NoRotation <: Rotation end
type RoundRotation <: Rotation end
type FullRotation <: Rotation end

immutable State{W<:Unsigned, R<:Rotation}
    r::Uint8
    k::Array{Uint8}
    s::Array{W}
    rotate::Type{R}
end

State{R<:Rotation}(w::Type{Uint8}, r::Uint8, k::Array{Uint8}; 
      rotate::Type{R}=FullRotation) = 
State{w, R}(r, k, expand_key(r, k, P8, Q8), rotate)

State{R<:Rotation}(w::Type{Uint16}, r::Uint8, k::Array{Uint8}; 
      rotate::Type{R}=FullRotation) = 
State{w, R}(r, k, expand_key(r, k, P16, Q16), rotate)

State{R<:Rotation}(w::Type{Uint32}, r::Uint8, k::Array{Uint8}; 
      rotate::Type{R}=FullRotation) = 
State{w, R}(r, k, expand_key(r, k, P32, Q32), rotate)

State{R<:Rotation}(w::Type{Uint64}, r::Uint8, k::Array{Uint8}; 
      rotate::Type{R}=FullRotation) = 
State{w, R}(r, k, expand_key(r, k, P64, Q64), rotate)

function parse_state{W<:Unsigned}(::Type{W}, s)
    if in(',', s)
        map(x -> parseint(W, x, 16), split(s, ','))
    else
        # old format was without commas
        collect(W, pack(W, hex2bytes(s), little=false))
    end
end

# create with a known state (no key)
State{W<:Unsigned, R<:Rotation}(r::Uint, s::Array{W}; 
                                rotate::Type{R}=FullRotation) = 
                                State{W, R}(r, Uint8[], s, rotate)

State{W<:Unsigned, R<:Rotation}(::Type{W}, r::Uint, s::String; 
                                rotate::Type{R}=FullRotation) = 
                                State{W, R}(r, Uint8[], parse_state(W, s), rotate)

sprintf_state{W<:Unsigned}(s::State{W}) = join(map(pad, s.s), ",")

function Base.show{W<:Unsigned}(io::IO, s::State{W})
    print(io, @sprintf("RC5-%d/%d/%d 0x%s s:%s", 
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

rotatel{W<:Unsigned}(::Type{NoRotation}, a::W, b::W, i::Unsigned) = a

rotatel{W<:Unsigned}(::Type{RoundRotation}, a::W, b::W, i::Unsigned) = rotatel(a, i)

rotatel{W<:Unsigned}(::Type{FullRotation}, a::W, b::W, i::Unsigned) = rotatel(a, b)


function expand_key{W<:Unsigned}(r::Uint8, k::Array{Uint8}, p::W, q::W)
    u = sizeof(W)
    b = length(k)
    c::Uint8 = ceil(b / u)
    l = zeros(W, c)
    for i = (b-1):-1:0
        l[div(i, u)+1] = (l[div(i, u)+1] << 8) + k[i+1]
    end
    t = 2(r+1)
    s = zeros(W, t)
    s[1] = p
    for i = 2:t
        s[i] = s[i-1] + q
    end
    i = j = 0
    a::W, b::W = 0x0, 0x0
    for _ = 1:3*max(t, c)
        s[i+1] = rotatel(convert(W, s[i+1] + (a + b)), 0x3)
        a = s[i+1]
        l[j+1] = rotatel(convert(W, l[j+1] + (a + b)), a + b)
        b = l[j+1]
        i = (i+1) % t
        j = (j+1) % c
    end
    s
end

function encrypt{W<:Unsigned}(s::State{W}, a::W, b::W)
    # encrypt two half-blocks
#    println("a $(pad(a)) + $(pad(s.s[1]))")
    a::W = a + s.s[1]
#    println("b $(pad(b)) + $(pad(s.s[2]))")
    b::W = b + s.s[2]
    for i in 0x1:s.r
#        println("a $(pad(a)) x $(pad(b))")
        a = a $ b
        a = rotatel(s.rotate, a, b, i)
#        println("a $(pad(a)) + $(pad(s.s[2i+1]))")
        a = a + s.s[2i+1]
#        println("b $(pad(b)) x $(pad(a))")
        b = b $ a
        b = rotatel(s.rotate, b, a, i)
#        println("b $(pad(b)) + $(pad(s.s[2i+2]))")
        b = b + s.s[2i+2]
    end
    a, b
end

function encrypt{W<:Unsigned}(s::State{W}, plain)
    # encrypt a stream of bytes
    e = Task() do
        for ab in group(2, pack(W, plain))
            a, b = encrypt(s, ab[1], ab[2])
            produce(a)
            produce(b)
        end
    end
    unpack(W, e)
end


# various solutions

include("r0.jl")
include("r1_noro.jl")
include("lbits_noro.jl")
include("search_noro.jl")
include("ga_noro.jl")
include("dfs_noro.jl")
include("cached_dfs_noro.jl")
include("ripple.jl")
include("search_roundro.jl")


# ---- validate solutions

make_keygen(w, r, k; rotate=FullRotation) = 
() -> State(w, r, collect(Uint8, take(k, rands(Uint8))), rotate=rotate)
fake_keygen(w, r, k; rotate=FullRotation) = 
() -> State(w, r, collect(Uint8, take(k, constant(0x0))), rotate=rotate)

function solutions()
    # no rotation and zero rounds 
    key_from_encrypt(3, make_solve_r0(Uint32, 0x2), 
                     make_keygen(Uint32, 0x0, 0x2),
                     k -> ptext -> encrypt(k, ptext), eq=same_state)
    # one rotation, exact back-calculation, 8 bits
    key_from_encrypt(3, make_solve_r1_noro(Uint8), 
                     make_keygen(Uint8, 0x1, 0x2, rotate=NoRotation),
                     k -> (a, b) -> encrypt(k, a, b), 
                     eq=same_ctext(16, encrypt))
    # one rotation, exact back-calculation, 32 bits
    key_from_encrypt(3, make_solve_r1_noro(Uint32), 
                     make_keygen(Uint32, 0x1, 0x2, rotate=NoRotation),
                     k -> (a, b) -> encrypt(k, a, b),
                     eq=same_ctext(16, encrypt))
    # tabulate first bit (only) in 8-bit table with 8-bit blocks
    ptext_from_encrypt(3, make_solve_lbits_noro(Uint8, 1, Uint8), 
                       make_keygen(Uint8, 0x1, 0x2, rotate=NoRotation),
                       k -> p -> encrypt(k, p), 16,
                       eq=same_ptext(Uint32, 1),
                       encrypt2=k -> (a, b) -> encrypt(k, a, b))
    # tabulate 9 bits in 16-bit table with 32-bit blocks
    ptext_from_encrypt(3, make_solve_lbits_noro(Uint16, 9, Uint32), 
                       make_keygen(Uint32, 0x3, 0x10, rotate=NoRotation),
                       k -> p -> encrypt(k, p), 32,
                       eq=same_ptext(Uint32, 9),
                       encrypt2=k -> (a, b) -> encrypt(k, a, b))
    # adaptive 8 bits, no rotation, 1 round
    ptext_from_encrypt(3, make_search_noro(Uint8), 
                       make_keygen(Uint8, 0x1, 0x2, rotate=NoRotation),
                       k -> p -> encrypt(k, p), 16,
                       eq=same_ptext(),
                       encrypt2=k -> (a, b) -> encrypt(k, a, b))
    # adaptive 32 bits, no rotation, 16 rounds
    ptext_from_encrypt(3, make_search_noro(Uint32), 
                       make_keygen(Uint32, 0x10, 0x10, rotate=NoRotation),
                       k -> p -> encrypt(k, p), 32,
                       eq=same_ptext(),
                       encrypt2=k -> (a, b) -> encrypt(k, a, b))
    # GA, 8 bits, no rotation, 2 rounds
#    key_from_encrypt(1, make_ga_noro(Uint8, 0x2, 0x10, 256, 100000, 1000, 100),
#                     make_keygen(Uint8, 0x2, 0x10, rotate=NoRotation),
#                     k -> ptext -> encrypt(k, ptext), 
#                     eq=same_ctext(256, encrypt))
    # GA, 32 bits, no rotation, 1 round
#    key_from_encrypt(1, make_ga_noro(Uint32, 0x1, 0x10, 256, 100000, 1000, 100),
#                     make_keygen(Uint32, 0x1, 0x10, rotate=NoRotation),
#                     k -> ptext -> encrypt(k, ptext), 
#                     eq=same_ctext(256, encrypt))
    # DFS, 8 bits, no rotation, 1 round
    key_from_encrypt(3, make_dfs_noro(Uint8, 0x1, 32),
                     make_keygen(Uint8, 0x1, 0x10, rotate=NoRotation),
                     k -> (a, b) -> encrypt(k, a, b), 
                     eq=same_ctext(64, encrypt))
    # DFS, 32 bits, no rotation, 4 rounds
    key_from_encrypt(1, make_dfs_noro(Uint32, 0x4, 32),
                     make_keygen(Uint32, 0x4, 0x10, rotate=NoRotation),
                     k -> (a, b) -> encrypt(k, a, b), 
                     eq=same_ctext(1024, encrypt))
    # DFS w table, 32 bits, no rotation, 5 rounds (~100 min)
    table1, table2 = precalc2()
    key_from_encrypt(1, make_cached_dfs_noro_r5(Uint32, table1, table2),
                     fake_keygen(Uint32, 0x5, 0x10, rotate=NoRotation),
                     k -> (a, b) -> encrypt(k, a, b), 
                     eq=same_ctext(1024, encrypt))
    # DFS w table, 32 bits, no rotation, 8 rounds (does not complete)
#    key_from_encrypt(1, make_cached_dfs_noro_r8(Uint32, table1, table2, period=10),
#                     fake_keygen(Uint32, 0x8, 0x10, rotate=NoRotation),
#                     k -> (a, b) -> encrypt(k, a, b), 
#                     eq=same_ctext(1024, encrypt))
    # local search
    ptext_from_encrypt(3, make_search_roundro(Uint32, 3), 
                       make_keygen(Uint32, 0x3, 0x2, rotate=RoundRotation),
                       k -> p -> encrypt(k, p), 32,
                       eq=same_ptext(),
                       encrypt2=k -> (a, b) -> encrypt(k, a, b))
    return
end


# ---- tests (for main code; tests are also in each solution)

function test_rotatel()
    y = rotatel(0x81, 0x1)
    @assert y == 0x03 y
    y = rotatel(0x81, 0x9)
    @assert y == 0x03 y
    y = rotatel(0x81, 0x81)
    @assert y == 0x03 y
    println("test_rotate ok")
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
    println("test_vectors ok")
end

function test_8()
    # just checking the code runs (correct values unknown)
    a, b = encrypt(State(Uint8, 0x0c, zeros(Uint8, 16)), 0x00, 0x00)
    @assert a == 0xa6 a
    @assert b == 0xea b
    println("test_8 ok")
end

function assert_cache{W<:Unsigned}(cache, state::State{W})
    println("$state")
    a::W, b::W = 0x1, 0x2
    c, d = encrypt(state, a, b)
    e, f = encrypt(cache, state, a, b)
    println("$W $(state.r)  $(pad(a)) $(pad(b))  $(pad(c)) $(pad(d))  $(pad(e)) $(pad(f))")
    @assert c == e a
    @assert d == f b
end

function test_set()
    @assert 0x2 == set(ZERO, 2, ONE)
    @assert 0x6 == set(ZERO, 2, THREE, 2)
    println("test_set ok")
end

function test_table1(table1)
    for ab in ZERO:THREE
        state = State(convert(Uint, 0x2), zeros(Uint8, 6), rotate=NoRotation)
        for s in ZERO:convert(Uint, 0x3f)
            set_state!(state, convert(Uint8, s), ONE)
            a, b = encrypt(state, convert(Uint8, ab & 0x1), convert(Uint8, ab & 0x2 >> 1))
            cd = table1[(ab | s << 8)+1]
            @assert cd & 0x3 == (a & 0x1) | (b & 0x1 << 1)
        end
    end
    println("test_table ok")
end

function test_table2(table1, table2)
    m = 0x3f00
    for ab in ZERO:THREE
        state = State(convert(Uint, 0x5), zeros(Uint8, 12), rotate=NoRotation)
        for s in ZERO:convert(Uint, 0xfff)
            set_state!(state, convert(Uint16, s), ONE)
            a, b = encrypt(state, convert(Uint8, ab & 0x1), convert(Uint8, ab & 0x2 >> 1))
            out1 = table1[(ab | (m & (s << 8)))+1]
            cd = table2[((out1 & 0x3) | (m & (s << 2)))+1]
#            println("$(pad(s)) $cd $(a & 0x1 | (b & 0x1 << 1))")
            @assert cd & 0x3 == (a & 0x1) | (b & 0x1 << 1)
        end
    end
    println("test_table2 ok")
end

function test_chars()
    # test strange result
    # level 31  33 37 42 49 37 48 38 37 41 62 46 63 24 49 7 63 15 45 3 32 36 40 56 17 18 8 6 32 47 6 39 52 20 3 16 4 1 6 46 10 60 32 54 4 24 59 19 37 0 1 7 24 6 51 8 23 0 5 3 36
    # RC5-32/5/0 0x s:1a3049ebb8d360b01df181b90540ddb0c1d240f6a41ce7ffd963eb95348d3baa13f1f5ac6a4389729dc4984014a6cc3f
    # RC5-32/5/0 0x s:bdc109eb2c4d40b078a6c1b9224815b00e4088f664d0a7ff6284c39566a8f3aa4639e5ac0858497200f318400038cc3f
    t1 = "1a3049ebb8d360b01df181b90540ddb0c1d240f6a41ce7ffd963eb95348d3baa13f1f5ac6a4389729dc4984014a6cc3f"
    t2 = "bdc109eb2c4d40b078a6c1b9224815b00e4088f664d0a7ff6284c39566a8f3aa4639e5ac0858497200f318400038cc3f"
    s1 = State(Uint32, FIVE, t1, rotate=NoRotation)
    println("$t1\n$s1")
    s2 = State(Uint32, FIVE, t2, rotate=NoRotation)
    println("$t2\n$s2")
    p = collect(Uint8, take(40, rands(Uint8)))
    c1 = collect(Uint8, encrypt(s1, p))
    c2 = collect(Uint8, encrypt(s2, p))
    println(bytes2hex(c1))
    println(bytes2hex(c2))
    for (a, b) in [(typemin, typemin), (typemax, typemax), (typemin, typemax), (typemax, typemin)]
        a, b = a(Uint32), b(Uint32)
        ap1, bp1 = encrypt(s1, a, b)
        ap2, bp2 = encrypt(s2, a, b)
        println("$(pad(a)) $(pad(b))  $(pad(ap1)) $(pad(bp1))  $(pad(ap2)) $(pad(bp2))")
    end
    for (a, b) in take(4, group(2, rands(Uint32)))
        a, b = convert(Uint32, a), convert(Uint32, b)
        ap1, bp1 = encrypt(s1, a, b)
        ap2, bp2 = encrypt(s2, a, b)
        println("$(pad(a)) $(pad(b))  $(pad(ap1)) $(pad(bp1))  $(pad(ap2)) $(pad(bp2))")
    end
    for (a, b) in spirals(Uint32)
        ap1, bp1 = encrypt(s1, a, b)
        ap2, bp2 = encrypt(s2, a, b)
        println("$(pad(a)) $(pad(b))  $(pad(ap1)) $(pad(bp1))  $(pad(ap2)) $(pad(bp2))")
    end
    println("test_chars ok")
end


function tests()
    test_rotatel()
    test_vectors()
    test_8()
    test_set()
    table1, table2 = precalc2()
    test_table1(table1)
    test_table2(table1, table2)
    test_cached_dfs_r5(table1, table2)
    test_chars()
    test_trace()
    prove_carry(Uint8, 0x3, 2, 10000)
    prove_nonlinear(Uint8, 0x3, 2, 10000)
    test_influence(Uint32, 0x5)
    test_influence(Uint32, 0x6)
    test_common_bits()
    test_local_search(0x3)
#    test_local_search(0x6)
end


end
