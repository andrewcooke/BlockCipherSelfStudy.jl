
module RC5
using Blocks, Solve, Tasks, Debug, GA


# this includes a definition of RC5 (with and without rotation, but no
# decryption, currently) and an implementation of the following attacks:
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

immutable State{W<:Unsigned}
    r::Uint8
    k::Array{Uint8}
    s::Array{W}
    rotate::Bool
end

State(w::Type{Uint8}, r::Uint8, k::Array{Uint8}; rotate=true) = 
State{w}(r, k, expand_key(r, k, P8, Q8), rotate)

State(w::Type{Uint16}, r::Uint8, k::Array{Uint8}; rotate=true) = 
State{w}(r, k, expand_key(r, k, P16, Q16), rotate)

State(w::Type{Uint32}, r::Uint8, k::Array{Uint8}; rotate=true) = 
State{w}(r, k, expand_key(r, k, P32, Q32), rotate)

State(w::Type{Uint64}, r::Uint8, k::Array{Uint8}; rotate=true) = 
State{w}(r, k, expand_key(r, k, P64, Q64), rotate)

# create with a known state (no key)
State{W<:Unsigned}(r::Uint8, s::Array{W}; rotate=true) = 
State{W}(r, Uint8[], s, rotate)

sprintf_state{W<:Unsigned}(s::State{W}) = join(map(pad, s.s), "")

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
rotatel{W<:Unsigned}(::Type{W}, x::Integer, n::Integer) = 
rotatel(convert(W, x), n)

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
        s[i+1] = rotatel(W, s[i+1] + (a + b), 0x3)
        a = s[i+1]
        l[j+1] = rotatel(W, l[j+1] + (a + b), a + b)
        b = l[j+1]
        i = (i+1) % t
        j = (j+1) % c
    end
    s
end

function encrypt{W<:Unsigned}(s::State{W}, a::W, b::W)
    # encrypt two half-blocks
    a::W = a + s.s[1]
    b::W = b + s.s[2]
    for i = 1:s.r
        a = a $ b
        if s.rotate
            a = rotatel(W, a, b)
        end
        a = a + s.s[2i+1]
        b = b $ a
        if s.rotate
            b = rotatel(W, b, a)
        end
        b = b + s.s[2i+2]
    end
    a, b
end

function encrypt{W<:Unsigned}(s::State{W}, plain)
    # encrypt a stream of bytes
    e = Task() do
        for ab in group(2, pack(W, plain))
            c, d = encrypt(s, ab...)
#            println("$(pad(ab[1])) $(pad(ab[2])) -> $(pad(c)) $(pad(d))")
            produce(c)
            produce(d)
        end
    end
    unpack(W, e)
end


# ---- 0 round solution

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


# ---- 1 round no rotation solution

function r1_noro{W<:Unsigned}(a::W, b::W, s1::W, s2::W, s3::W, s4::W)
    a = a + s1
    b = b + s2
    a = (a $ b) + s3
    b = (b $ a) + s4
    a, b
end

function make_solve_r1_noro{W<:Unsigned}(::Type{W})
    function solve(e)
        # a' = ((a + s[1]) $ (b + s[2])) + s[3]
        # a0'-a1' = ((a0 + s[1]) $ (b0 + s[2])) - ((a1 + s[1]) $ (b1 + s[2]))
        # choose b0 == b1 = 0
        # a0'-a1' = ((a0 + s[1]) $ s[2]) - ((a1 + s[1]) $ s[2])
        # choose a0 and a1 to be same except for 1 bit - can get bit for s[2]
        # except for msb; see Experiment.jl
        k::W = 0x0
        m::W = 0x0
        # find bit using differences (see Experiment.jl)
        for b = 0:(8*sizeof(W)-1)
            m = m == 0 ? 1 : m << 1
            while true
                a0::W = rand(W)
                a1::W = a0 - m  # minus here
                ap0, _ = e(a0, convert(W, 0x0))
                ap1, _ = e(a1, convert(W, 0x0))
                d = convert(Int64, ap0) - convert(Int64, ap1)
                if d == m  # subtract and find, so bit zero
 #                   println("bit $b of s2 0: $(pad(k))")
                    break
                end
                a1 = a0 + m  # plus here
                ap0, _ = e(a0, convert(W, 0x0))
                ap1, _ = e(a1, convert(W, 0x0))
                d = convert(Int64, ap0) - convert(Int64, ap1)
                if d == m  # add and find, so bit one
                    k = k+m
#                    println("bit $b of s2 1: $(pad(k))")
                    break
                end
            end
        end
        # at this point we know k (s[2]) except for msb (m)
        for s2::W in (k, k+m)
            # if we know s[2], set b0+s[2]=0, b1+s[2]=0xf..f, a0=0, a1=0
            # a0'-a1' = ((a0+s[1]) $ (b0+s[2])) - ((a1+s[1]) $ (b1+s[2]))
            #         = (s[1] - (s[1] $ 0xf..f))
            #         = s[1] - (-s[1]-1)
            ap0, _ = e(convert(W, 0x0), convert(W, -s2))
            ap1, _ = e(convert(W, 0x0), convert(W, -1-s2))
#            println("a0' $(pad(ap0))  a1' $(pad(ap1))")
            s1l7::W = convert(W, ap0 - ap1 - 1) >> 1  # don't know top bit
            for s1::W in (s1l7, s1l7+0x80)
                s3::W = ap0 - s1
		u::W, v::W = rand(W), rand(W)
                up::W, vp::W = e(u, v)
		s4::W = convert(W, vp - (convert(W, v + s2) $ up))
                println("if s2=$(pad(s2)) and s1=$(pad(s1)) then s3=$(pad(s3)) and s4=$(pad(s4))")
                # check if the current s1,2,3 are ok
                i, ok = 0, true
                while ok && i < 10
		    u, v = rand(W), rand(W)
                    up, vp = e(u, v)
                    upp::W, vpp::W = r1_noro(u, v, s1, s2, s3, s4)
#		    println("$(pad(up)) $(pad(upp)) $(pad(vp)) $(pad(vpp))")
                    ok = up == upp && vp == vpp
		    i = i+1
		end
		if ok
                   # pack final state
                   s = State(0x1, W[s1, s2, s3, s4], rotate=false)
		   println("result $s")
                   return s
		else
		   println("bad check")
                end
            end
        end
        error("failed to find solution")
    end
end


# ---- lowest bits directly

function make_solve_lbits_noro{W<:Unsigned, T<:Unsigned}(::Type{T}, nbits, ::Type{W})

    # for any number of rounds, or key size, but no rotation, we can
    # tabulate the the first nbits of each half-block and use them as
    # a lookup table.  this doesn't decrypt the entire block, but typically
    # gives two bytes in every 8.

    @assert nbits <= 8 * sizeof(T)  # storage must be big enough
    @assert sizeof(T) <= sizeof(W)
    n = 2 ^ nbits
    m = n - 1

    function solve(ctext, e)

        table = Array(T, n, n, 2)
        for i in 0:(n-1)
            a = convert(W, i)
            for j in 0:(n-1)
                b = convert(W, j)
                ap, bp = e(a, b)
                ap, bp = ap & m, bp & m
#                println("$(pad(a)) $(pad(b)) <- $(pad(ap)) $(pad(bp))")
                table[ap+1, bp+1, 1] = convert(T, a)
                table[ap+1, bp+1, 2] = convert(T, b)
            end
        end

        Task() do
            for ab in group(2, pack(W, ctext))
                a::W, b::W = ab
                ap::W, bp::W = a & m, b & m
                c::W, d::W = table[ap+1, bp+1, 1:2]
#                println("$(pad(a)) $(pad(b)) -> $(pad(ap)) $(pad(bp)) -> $(pad(c)) $(pad(d))")
                produce_from(unpack(W, convert(W, (a & ~m) | c)))
                produce_from(unpack(W, convert(W, (b & ~m) | d)))
            end
        end
    end
end

function make_check_table(nbits, nbytes)
    function check_table{W<:Unsigned}(s::State{W}, detab)
        ptext = collect(Uint8, take(nbytes, rands(Uint8)))
        ptextw1 = pack(W, ptext)
        ptextw2 = detab(encrypt(s, ptext))
        m::W = 2^nbits - 1
        ok = true
        for (p1, p2) in zip(ptextw1, ptextw2)
 #           println("$(pad(p1))/$(pad(p1 & m)) $(pad(p2))/$(pad(p2 & m))")
            ok = ok && p1 & m == p2 & m
        end
        ok
    end
end


# ---- adaptive search bit by bit from lsb

function make_search_noro{W<:Unsigned}(::Type{W})

    # full adaptive decryption.  given two half-blocks we test-encrypt
    # possible combinations for the lsb, then the next bit, etc, until
    # we have all bits.

    function solve(ctext, e)
        Task() do
            for (a, b) in group(2, pack(W, ctext))
                bit::W = 1
                ap::W, bp::W = 0x0, 0x0
                for i in 1:8*sizeof(W)
                    for c::W in [0x0, bit]
                        for d::W in [0x0, bit]
                            cp, dp = e(ap | c, bp | d)
                            if cp & bit == a & bit && dp & bit == b & bit
                                ap, bp = ap | c, bp | d
                            end
                        end
                    end
                    bit = bit << 1
                end
#                println("$(pad(a)) $(pad(b)) -> $(pad(ap)) $(pad(bp))")
                produce_from(unpack(W, ap))
                produce_from(unpack(W, bp))
            end
        end
    end
end


# ---- genetic algorithm to derive state

# the "real" score is the float; the ints are to show how many of each bit
# we have encoded correctly and to assess completness (and so target mutation)
typealias Score (Float64, Vector{Int})

# for sorting of (Score, Individual)
Base.isless{W<:Unsigned}(s1::State{W}, s2::State{W}) = false
Base.isless(a1::Vector{Int}, a2::Vector{Int}) = 
length(a1) == length(a2) && length(a1) > 0 && 
(a1[1] < a2[1] || (a1[1] == a2[1] && length(a1) > 1 && a1[2:] < a2[2:]))

# custom state added to the population
type Context
    total::Float64        # total score for entire population
    lowest::Float64       # lowest score of entire population
    complete::Int         # number of bts that appear correct
    limit::Int            # maximum number of iterations
    ctext::Vector{Uint8}  # target ctext...
    ptext::Vector{Uint8}  # ...from this ptext
end

function GA.prepare!{W<:Unsigned}(p::Population{Context, State{W}, Score})
    scores = collect(Float64, map(pair -> pair[1][1], p.sorted))
    # used for weighting in select
    p.context.total = sum(scores) 
    p.context.lowest = minimum(scores)
    # used for targetting mutation
    p.context.complete = 0
    while p.context.complete < 8*sizeof(W) && 
        p.sorted[1][1][2][p.context.complete+1] == length(p.context.ptext) / sizeof(W)
        p.context.complete = p.context.complete + 1
    end
    println("before: $(p.context.complete) $(p.sorted[1][1]) / $(p.context.total)")
end

function GA.select{S<:State}(p::Population{Context, S, Score})
    # weight by score over minimum.
    r = rand() * (p.context.total - p.size * p.context.lowest)
    for ((s, g), i) in p.sorted
        r = r - (s - p.context.lowest)
        if r <= 0
            return i
        end
    end
    @assert false "no selection"
end

function GA.breed{W<:Unsigned}(c::Context, s1::State{W}, s2::State{W})
    b1, b2 = rand(0:8*sizeof(W)-1, 2)
    b1, b2 = min(b1, b2), max(b1, b2)
    # banded crossover - block of state for a range of bits
    m::W = 2^b2-1 - (2^b1-1)
    State(s1.r, W[(s[1]&m)|(s[2]&~m) for s in zip(s1.s, s2.s)], rotate=false)
end

function GA.mutate{W<:Unsigned}(c::Context, s::State{W})
    for x in 1:rand(1:2)
        # target the "next" bit after complete, with some lower bits for carry.
        lo = rand(1:max(1, c.complete))
        hi = min(c.complete+1, 8*sizeof(W))
        mask::W = 1 << (rand(lo:hi) - 1)
        for y in 1:rand(1:3)
            # multiple hits on same bit - 2 will often perserve parity
            i = rand(1:length(s.s))
            s.s[i] = s.s[i] $ mask
        end
    end
    s
end

function GA.complete{W<:Unsigned}(age, p::Population{Context, State{W}, Score})
    println("after: $(p.sorted[1][1]), $(p.sorted[end][1][1]) at $(p.generation)")
    return p.generation >= p.context.limit || 
    p.sorted[1][1][2] == length(p.context.ptext)/sizeof(W)*ones(Int, 8*sizeof(W))
end

function GA.score{W<:Unsigned}(c::Context, s::State{W})
    ctext = collect(Uint8, encrypt(s, c.ptext))
    score, good = 0.0, zeros(Int, 8*sizeof(W))
    for (c1, c2) in zip(pack(W, ctext), pack(W, c.ctext))
        bits::W, w, bit::W = c1 $ c2, 1.0, 1
        for i in 1:8*sizeof(W)
            if bits & bit == 0
                score = score + w
                good[i] = good[i] + 1
            else
                # contiguous correct bits from lsb receive maximum score
                w = w / 10.0
            end
            bit = bit << 1
        end
    end
    (score, good)
end

function make_solve_ga_noro{W<:Unsigned}(::Type{W}, r, k, len, limit, size, nchild)
    @assert len % sizeof(W) == 0
    function solve(e)
        ptext = collect(Uint8, take(len, rands(Uint8)))
        ctext = collect(Uint8, e(ptext))
        s = [State(W, r, collect(Uint8, take(k, rands(Uint8))), rotate=false)
             for _ in 1:size]
        p = Population(Context(0, 0, 0, limit, ctext, ptext), s, nchild, Score)
        age, p = evolve(p)
        p.sorted[1][2]
    end
end


# ---- dfs of state

# the search proceeds from lsb to msb.  the nodes at each level correspond to
# the binary values (increasing from zero) for the state for that bit.

# at each level, half-blocks are encrypted and checked for the bits populated
# so far.  at each level we check len random blocks.

function uint_for_bits(n)
    for u in (Uint8, Uint16, Uint32, Uint64)
        if 8 * sizeof(u) >= n
            return u
        end
    end
    error("no uint")
end

function test_bits{W<:Unsigned}(ptext, ctext, state::State{W}, level)
    mask::W = convert(W, 1 << level) - 1
    for ((a, b), (a1, b1)) in zip(ptext, ctext)
        (a2, b2) = encrypt(state, a, b)
        if a1 & mask != a2 & mask || b1 & mask != b2 & mask
            return false
        end
    end
    true
end

function set_state{W<:Unsigned, U<:Unsigned}(state::State{W}, tree::Vector{U}, width, level)
    # copy the data from the current tree level into the state
    # inverting or reversing (msb/lsb) the tree bits doesn't change speed
    wbit::W, ubit::U = 1 << (level-1), 1
    for i in 1:width
        if tree[level] & ubit == 0
            state.s[i] = state.s[i] & ~wbit
        else
            state.s[i] = state.s[i] | wbit
        end
        ubit = ubit << 1
    end
end

function make_solve_dfs_noro{W<:Unsigned}(::Type{W}, r, len)
    function solve(e)
        ptext = collect((W, W), group(2, take(2*len, rands(W))))
        ctext = (W,W)[e(a, b) for (a, b) in ptext]
        width, depth = 2r+2, 8*sizeof(W)
        U = uint_for_bits(width+1)  # extra bit for overflow
        state = State(r, zeros(W, width), rotate=false)
        tree = zeros(U, depth)
        level, overflow::U = 1, 1 << width
        while level > 0 && level <= depth
            set_state(state, tree, width, level)
            tree[level] = tree[level] + 1
            if test_bits(ptext, ctext, state, level)
                println("$level/$depth $(pad(tree[level])) $(bytes2hex(collect(Uint8, unpack(state.s))))")
                level = level + 1
            else
                # will try next node
            end
            while level > 0 && level <= depth && tree[level] == overflow
                tree[level], level = 0, level - 1
            end
        end
        for i in 1:depth
            println("$i $(pad(tree[i]))")
        end
        state
    end
end

function make_solve_beam_noro{W<:Unsigned}(::Type{W}, r, len)
    # restrict dfs to limit choices at any level, and then increase
    # limit slowly.  so forces earlier levels to backtrack if a lower
    # level "can find no solution".  slows things down.
    function solve(e)
        ptext = collect((W, W), group(2, take(2*len, rands(W))))
        ctext = (W,W)[e(a, b) for (a, b) in ptext]
        width, depth = 2r+2, 8*sizeof(W)
        U = uint_for_bits(width+1)  # extra bit for overflow
        state = State(r, zeros(W, width), rotate=false)
        overflow::U = 1 << width
        for limit in [1 << w for w in 1:width]
            tree, level, beam = zeros(U, depth), 1, zeros(Int, depth)
            while level > 0
                set_state(state, tree, width, level)
                save, tree[level] = tree[level], tree[level] + 1
                if test_bits(ptext, ctext, state, level)
                    println("$(beam[level])/$limit $level/$depth $(pad(save)) $(bytes2hex(collect(Uint8, unpack(state.s))))")
                    beam[level], level = beam[level] + 1, level + 1
                    if level > depth
                        for i in 1:depth
                            println("$i $(pad(tree[i])) $(beam[i])")
                        end
                        return state
                    else
                        beam[level] = 0
                    end
                else
#                    println("$(beam[level])/$limit $level/$depth $(pad(save))")
                end
                while level > 0 && (beam[level] > limit || tree[level] == overflow)
                    tree[level], level = 0, level - 1
                end
            end
         end
        error("no solution")
    end
end


# ---- validate solutions

make_keygen(w, r, k; rotate=true) = 
() -> State(w, r, collect(Uint8, take(k, rands(Uint8))), rotate=rotate)
fake_keygen(w, r, k; rotate=true) = 
() -> State(w, r, collect(Uint8, take(k, constant(0x0))), rotate=rotate)

function solutions()
    key_from_encrypt(1, make_solve_dfs_noro(Uint32, 0x6, 64),
                     make_keygen(Uint32, 0x6, 0x10, rotate=false),
                     k -> (a, b) -> encrypt(k, a, b), 
                     eq=same_ctext(16, encrypt))
    return
    # no rotation and zero rounds
    key_from_encrypt(3, make_solve_r0(Uint32, 0x2), 
                     make_keygen(Uint32, 0x0, 0x2),
                     k -> ptext -> encrypt(k, ptext), eq=same_state)
    # one rotation, exact back-calculation, 8 bits
    key_from_encrypt(3, make_solve_r1_noro(Uint8), 
                     make_keygen(Uint8, 0x1, 0x2, rotate=false),
                     k -> (a, b) -> encrypt(k, a, b), 
                     eq=same_ctext(16, encrypt))
    # one rotation, exact back-calculation, 32 bits
    key_from_encrypt(3, make_solve_r1_noro(Uint32), 
                     make_keygen(Uint32, 0x1, 0x2, rotate=false),
                     k -> (a, b) -> encrypt(k, a, b),
                     eq=same_ctext(16, encrypt))
    # tabulate first bit (only) in 8-bit table with 8-bit blocks
    ptext_from_encrypt(3, make_solve_lbits_noro(Uint8, 1, Uint8), 
                       make_keygen(Uint8, 0x1, 0x2, rotate=false),
                       k -> p -> encrypt(k, p), 16,
                       eq=same_ptext(Uint32, 1),
                       encrypt2=k -> (a, b) -> encrypt(k, a, b))
    # tabulate 9 bits in 16-bit table with 32-bit blocks
    ptext_from_encrypt(3, make_solve_lbits_noro(Uint16, 9, Uint32), 
                       make_keygen(Uint32, 0x3, 0x10, rotate=false),
                       k -> p -> encrypt(k, p), 32,
                       eq=same_ptext(Uint32, 9),
                       encrypt2=k -> (a, b) -> encrypt(k, a, b))
    # adaptive 8 bits, no rotation, 1 round
    ptext_from_encrypt(3, make_search_noro(Uint8), 
                       make_keygen(Uint8, 0x1, 0x2, rotate=false),
                       k -> p -> encrypt(k, p), 16,
                       eq=same_ptext(),
                       encrypt2=k -> (a, b) -> encrypt(k, a, b))
    # adaptive 32 bits, no rotation, 16 rounds
    ptext_from_encrypt(3, make_search_noro(Uint32), 
                       make_keygen(Uint32, 0x10, 0x10, rotate=false),
                       k -> p -> encrypt(k, p), 32,
                       eq=same_ptext(),
                       encrypt2=k -> (a, b) -> encrypt(k, a, b))
    # GA, 8 bits, no rotation, 2 rounds
    key_from_encrypt(3, make_solve_ga_noro(Uint8, 0x2, 0x10, 256, 100000, 1000, 100),
                     make_keygen(Uint8, 0x2, 0x10, rotate=false),
                     k -> ptext -> encrypt(k, ptext), 
                     eq=same_ctext(256, encrypt))
    # GA, 32 bits, no rotation, 1 round
    key_from_encrypt(3, make_solve_ga_noro(Uint32, 0x1, 0x10, 256, 100000, 1000, 100),
                     make_keygen(Uint32, 0x1, 0x10, rotate=false),
                     k -> ptext -> encrypt(k, ptext), 
                     eq=same_ctext(256, encrypt))
    # DFS, 8 bits, no rotation, 1 round
    key_from_encrypt(3, make_solve_dfs_noro(Uint8, 0x1, 32),
                     make_keygen(Uint8, 0x1, 0x10, rotate=false),
                     k -> (a, b) -> encrypt(k, a, b), 
                     eq=same_ctext(16, encrypt))
    # DFS, 32 bits, no rotation, 4 rounds
    key_from_encrypt(1, make_solve_dfs_noro(Uint32, 0x4, 32),
                     make_keygen(Uint32, 0x4, 0x10, rotate=false),
                     k -> (a, b) -> encrypt(k, a, b), 
                     eq=same_ctext(16, encrypt))
    # beam limited dfs (doesn't help)
    key_from_encrypt(3, make_solve_beam_noro(Uint8, 0x1, 32),
                     make_keygen(Uint8, 0x1, 0x10, rotate=false),
                     k -> (a, b) -> encrypt(k, a, b), 
                     eq=same_ctext(16, encrypt))
end


# ---- tests

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

function test_8()
    # just checking the code runs (correct values unknown)
    a, b = encrypt(State(Uint8, 0x0c, zeros(Uint8, 16)), 0x00, 0x00)
    @assert a == 0xa6 a
    @assert b == 0xea b
end

function tests()
    test_rotatel()
    test_vectors()
    test_8()
end


tests()
solutions()

end
