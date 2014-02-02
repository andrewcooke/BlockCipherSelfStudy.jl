
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
#                println("if s2=$(pad(s2)) and s1=$(pad(s1)) then s3=$(pad(s3)) and s4=$(pad(s4))")
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
                    s = State(ONE, W[s1, s2, s3, s4], rotate=NoRotation)
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
(a1[1] < a2[1] || (a1[1] == a2[1] && length(a1) > 1 && a1[2:end] < a2[2:end]))

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
    State(s1.r, W[(s[1]&m)|(s[2]&~m) for s in zip(s1.s, s2.s)], rotate=NoRotation)
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

function make_ga_noro{W<:Unsigned}(::Type{W}, r, k, len, limit, size, nchild)
    @assert len % sizeof(W) == 0
    function solve(e)
        ptext = collect(Uint8, take(len, rands(Uint8)))
        ctext = collect(Uint8, e(ptext))
        s = [State(W, r, collect(Uint8, take(k, rands(Uint8))), rotate=NoRotation)
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

function test_bits{W<:Unsigned}(ptext::Vector{(W,W)}, ctext::Vector{(W,W)}, state::State{W}, level::Uint)
    mask::W = convert(W, 1 << level) - 1
    # much faster than zip
    for i in 1:length(ptext)
        a, b = ptext[i]
        a1, b1 = ctext[i]
        a2, b2 = encrypt(state, a, b)
        if a1 & mask != a2 & mask || b1 & mask != b2 & mask
            return false
        end
    end
    true
end

function set_state!{W<:Unsigned, U<:Unsigned}(state::State{W}, row::U, level::Integer)
    bit::W, lsb::U, unset, width = one(W) << (level-1), one(U), zero(U), 2*state.r + 2
    for i in 1:width
        if row & lsb == unset
            state.s[i] = state.s[i] & ~bit
        else
            state.s[i] = state.s[i] | bit
        end
        row = row >> 1
    end
end

function make_dfs_noro{W<:Unsigned}(::Type{W}, r, len)
    function solve(e)
        ptext = collect((W, W), group(2, take(2*len, rands(W))))
        ctext = (W,W)[e(a, b) for (a, b) in ptext]
        width::Uint, depth::Uint = 2r+2, 8*sizeof(W)
        U = uint_for_bits(width+1)  # extra bit for overflow
        U = Uint64  # faster than minimum size above (left in for error check)
        state = State(convert(Uint, r), zeros(W, width), rotate=NoRotation)
        overflow::U, inc::U, start::U = 1 << width, one(U), zero(U)
        function inner(level)
            if level > depth
                true
            else
                row = start
                while row != overflow
                    set_state!(state, row, level)
                    if test_bits(ptext, ctext, state, level)
#                        println("$level/$depth $(pad(convert(U,tree[level]-0x1))) $(bytes2hex(collect(Uint8, unpack(state.s))))")
                        if inner(level + 1)
                            return true
                        end
                    end
                    row = row + inc
                end
                false
            end
        end
        if inner(one(Uint))
            state
        else
            error("no solution")
        end
    end
end


# ---- dfs for state using pre-calculated cache

# a lookup table (by bit, for all rounds) needs as key:
# - a, b
# - the state (2r+2 bits)
# - carry from the previous bit (2r+2 bits)
# the output is:
# - a, b (2 or 2r+2 for variable rounds)
# - carry to the next bit (2r+2 bits)

# r     0     1    2     3      4      6      8
# in    6     10   14    18     22     30     38
# out   4/4   6/8  8/12  10/16  12/20  16/28  20/36
# min   256B  1kB  16kB  512kB  

# if we ignore the zeroth round (ie for appending later rounds)

# r     1     2    3     4      6      8
# in    6     10   14    18     26     34
# out   4/4   6/8  8/12  10/16  12/20  16/28
# min   256B  1kB  16kB  512kB  

# if we want to get to 8 rounds AND store the zeroth round (earlier attempt
# didn't and it was ugly) then it seems like we need 3 table lookups, for 0-2,
# 3-5 and 6-8 (last two same table).  for 1B data with no intermediate results
# those are 16kB; if we store Uint64 then they will be 128kB.  i have l1=64kB,
# l2=256kB (both per core), and l3=2MB (shared).

# a previous attempt, storing intermediate results and handling zeroth round
# separately was very slow.

# so let's try with two small 16kB tables, aiming only for exact round counts
# (so 2, 5 or 8 rounds).  want core code to be very simple table lookups with
# minimal extra work.

# packing:
#   lsb  ab2 carries6 state6 msb
# this lets us directly carry over the result for lookup needing only a
# shift and add for state.

function set{W<:Unsigned}(word::W, bit::Int, value::Uint)
    mask::W = 1 << (bit - 1)
    return (word & ~mask) | (value & one(W)) << (bit - 1)
end

function set{W<:Unsigned}(word::W, bit::Int, value::W, len::Int)
    bit = bit - 1
    mask::W = one(W) << (bit+len) - (one(W) << bit) 
    return (word & ~mask) | ((value << bit) & mask)
end

# any way to have compact literal Uint apart from this?!
const ZERO = zero(Uint)
const ONE = one(Uint)
const TWO = ONE+ONE
const THREE = TWO+ONE
const FOUR = THREE+ONE
const FIVE = FOUR+ONE
const SIX = FIVE+ONE
const EIGHT = FOUR+FOUR
const SIXTEEN = FOUR*FOUR
const FIFTEEN = SIXTEEN-ONE

function precalc2()

    const SIZE = 2^14

    # cache a single round
    one_round = zeros(Uint, 2^6)
    for a in ZERO:ONE
        in = a
        for b in ZERO:ONE
            in = set(in, 2, b)
            for ca in ZERO:ONE
                in = set(in, 3, ca)
                for cb in ZERO:ONE
                    in = set(in, 4, cb)
                    for s1 in ZERO:ONE
                        in = set(in, 5, s1)
                        for s2 in ZERO:ONE
                            in = set(in, 6, s2)
                            A = a $ b
                            A = A + s1 + ca
                            B = (b $ A) & 0x1
                            B = B + s2 + cb
                            out = (A & 0x1) | (B & 0x1) << 1 | (A & 0x2) << 1 | (B & 0x2) << 2
                            one_round[in+1] = out
                        end
                    end
                end
            end
        end
    end

    # table including initial addition + 2 rounds
    table1 = zeros(Uint8, SIZE)   
    for a in ZERO:ONE
        in = a
        for b in ZERO:ONE
            in = set(in, 2, b)
            for c1 in ZERO:ONE
                in = set(in, 3, c1)
                for c2 in ZERO:ONE
                    in = set(in, 4, c2)
                    for s1 in ZERO:ONE
                        in = set(in, 9, s1)
                        A = a + s1 + c1
                        out = set(ZERO, 3, A >> 1)
                        in2 = A & 0x1
                        for s2 in ZERO:ONE
                            in = set(in, 10, s2)
                            B = b + s2 + c2
                            out = set(out, 4, B >> 1)
                            in2 = set(in2, 2, B)
                            for c34 in ZERO:THREE
                                in = set(in, 5, c34, 2)
                                in2 = set(in2, 3, c34, 2)
                                for s34 in ZERO:THREE
                                    in = set(in, 11, s34, 2)
                                    in2 = set(in2, 5, s34, 2)
                                    out2 = one_round[in2+1]
                                    out = set(out, 5, out2 >> 2, 2)
                                    in3 = out2 & 0x3
                                    for c56 in ZERO:THREE
                                        in = set(in, 7, c56, 2)
                                        in3 = set(in3, 3, c56, 2)
                                        for s56 in ZERO:THREE
                                            in = set(in, 13, s56, 2)
                                            in3 = set(in3, 5, s56, 2)
                                            out3 = one_round[in3+1]
                                            out = set(out, 7, out3 >> 2, 2)
                                            out = set(out, 1, out3, 2)
#                                            println("t1: $in -> $out")
                                            table1[in+1] = out
                                        end
                                    end
                                end
                            end
                        end
                    end
                end
            end
        end
    end

    # table including 3 rounds
    table2 = zeros(Uint8, SIZE)
    for ab in ZERO:THREE
        in = ab
        in1 = ab
        for c12 in ZERO:THREE
            in = set(in, 3, c12, 2)
            in1 = set(in1, 3, c12, 2)
            for s12 in ZERO:THREE
                in = set(in, 9, s12, 2)
                in1 = set(in1, 5, s12, 2)
                out1 = one_round[in1+1]
                out = set(ZERO, 3, out1 >> 2, 2)
                in2 = out1 & 0x3
                for c34 in ZERO:THREE
                    in = set(in, 5, c34, 2)
                    in2 = set(in2, 3, c34, 2)
                    for s34 in ZERO:THREE
                        in = set(in, 11, s34, 2)
                        in2 = set(in2, 5, s34, 2)
                        out2 = one_round[in2+1]
                        out = set(out, 5, out2 >> 2, 2)
                        in3 = out2 & 0x3
                        for c56 in ZERO:THREE
                            in = set(in, 7, c56, 2)
                            in3 = set(in3, 3, c56, 2)
                            for s56 in ZERO:THREE
                                in = set(in, 13, s56, 2)
                                in3 = set(in3, 5, s56, 2)
                                out3 = one_round[in3+1]
                                out = set(out, 7, out3 >> 2, 2)
                                out = set(out, 1, out3, 2)
#                                println("t2: $in -> $out")
                                table2[in+1] = out
                            end
                        end
                    end
                end
            end
        end
    end

    table1, table2
end

function spirals{W<:Unsigned}(::Type{W})
    # the idea here is to have each level have a different bit pattern,
    # to complement the basic test with a constant pattern.  however,
    # the results repeat every 8 bits.
    Task() do 
        for ab in ZERO:THREE
            ap, bp = zero(W), zero(W)
            for level in ONE:convert(Uint, 8*sizeof(W))
                cd = (ab + level) & THREE
                ap = ap | convert(W, (cd & ONE) << (level - 1))
                bp = bp | convert(W, ((cd & TWO) >> 1) << (level - 1))
            end
            produce(ap, bp)
        end
    end
end

function constants{W<:Unsigned}(::Type{W})
    const ALL_ONES::W, ALL_ZEROS::W = -1, 0
    Task() do
        for ab in ZERO:THREE
            produce(ab & ONE == ONE ? ALL_ONES : ALL_ZEROS,
                    ab & TWO == TWO ? ALL_ONES : ALL_ZEROS)
        end
    end
end

function make_cached_dfs_noro_r5{W<:Unsigned}(::Type{W}, table1, table2;
                                              initial=4, attempts=100, decay=0.1, period=1000)
    
    const DEPTH::Int = 8 * sizeof(W)
    const WIDTH::Uint = 2 * 5 + 2
    # tables of state require 6 bits offset 8 bits so generate and mask
    const SMASK::Uint = ((2 ^ 6) - 1) << 8
    const SDELTA::Uint = 1 << 8      
    # similar mask for carries
    const CMASK::Uint = ((2 ^ 6) - 1) << 2

    # memory budget (L1 is 64 kB):
    #  lookup tables, 2^14*2 = 16 kB * 2 = 32 kB
    #  known/carries, 2*DEPTH*N = 2*32*12 = 768 B
    #  score, N*8 = 76*12 = 912 B
    #  path, DEPTH*2*8 = 512 B
    #  state - not used til success

    function solve(e)

        const N::Int = initial + 8
        known = zeros(Uint8, 2, DEPTH, N)
        const score::Vector{Int} = zeros(Int, N)

         function set_known(a, b, ap, bp, i)
            for level in 1:DEPTH
                known[1, level, i] = bits(a, b)
                known[2, level, i] = bits(ap, bp)
                a, b, ap, bp = a >> 1, b >> 1, ap >> 1, bp >> 1
            end
        end

         function evaluate(s1::Uint, s2::Uint, level::Int, pattern::Int)
            in1::Uint = convert(Uint, known[1, level, pattern]) | s1
            out1::Uint = convert(Uint, table1[in1+ONE])
            k = convert(Uint, known[2, level, pattern])
            in2::Uint = (out1 & THREE) | (k & CMASK) | s2
            out2::Uint = convert(Uint, table2[in2+ONE])
            if out2 & THREE == k & THREE
                if level < DEPTH
                    known[1, level+1, pattern] = (known[1, level+1, pattern] & ~CMASK) | (out1 & CMASK)
                    known[2, level+1, pattern] = (known[2, level+1, pattern] & ~CMASK) | (out2 & CMASK)
                end
                true
            else
#                println("$level  $(s1 >> 8) $(s2 >> 8)  failed on $pattern")
                false
            end
        end

        # set initial known values (no carries)
        bits(a::W, b::W) = convert(Uint8, (a & one(W)) | (b & one(W) << 1))
        for (i, (a, b)) in enumerate(chain(constants(W), spirals(W), 
                                           group(2, take(2*initial, rands(W)))))
            ap, bp = e(a, b)
            set_known(a, b, ap, bp, i)
        end

        const path::Vector{Uint} = zeros(Uint, DEPTH*2)
        function fmt_path(level)
            p = ""
            for i in 1:2*(level-1)
                p = "$p $(path[i] >> 8)"
            end
            p
        end
        function extract(ab, p, pattern)
            val::W = zero(W)
            for level in 1:DEPTH
                val = val << 1
                val = val | (known[p, level, pattern] >> (ab - 1)) & 0x1
            end
            val
        end
        function print_pattern(pattern)
            a, b = extract(1, 1, pattern), extract(2, 1, pattern)
            println("$(pad(a)) $(pad(b))  $(score[pattern])")
        end
        function print_filter()
            for pattern in 1:N
                print_pattern(pattern)
            end
        end
        function fmt_brief()
            join(map(x -> "$x", score), " ")
        end
        function update_filter(level::Int)
            # returns the level to which we need to backtrack
            perm = sortperm(score, rev=true, alg=InsertionSort)
            known, score = known[:, :, perm], score[perm]
#            print_filter()
            for i = 1:N-1
                score[i] = convert(Int, floor(score[i] * decay))
            end
            score[N] = 0
            for j in 1:attempts
                a, b = rand(W), rand(W)
                ap, bp = e(a, b)
                set_known(a, b, ap, bp, N)
                for (l, (s2, s1)) in enumerate(take(level-1, group(2, path)))
                    if ! evaluate(s1, s2, l, N)
                        score[N] += 1
                        return l
                    end
                end
            end
#            print_pattern(N)
            level
        end

        function check(s1::Uint, s2::Uint, level::Int)
            for i in 1:N
                if ! evaluate(s1, s2, level, i)
                    score[i] += 1
                    return false
                end
            end
            true
        end

        counter::Uint = ZERO
        const state::State{W} = State(FIVE, zeros(W, WIDTH), rotate=NoRotation)
        function search(level::Int)
            # returns the level to which we must backtrack, or 0 on success
            backtrack::Int = 0
            counter = counter + ONE
            if counter == period || level > DEPTH
                println("$level $(fmt_path(level))")
#                print("$level $(fmt_path(level))    $(fmt_brief()) /")
                counter = ZERO
                # filter before exiting when level > DEPTH to run final check
                backtrack = update_filter(level)
#                println(" $(fmt_brief())")
                if backtrack < level
                    return backtrack
                elseif level > DEPTH
                    return 0
                end
            end
            # if we are not backtracking, search next level
            for s2 in ZERO:SDELTA:SMASK
                path[TWO*level-ONE] = s2
                for s1 in ZERO:SDELTA:SMASK
                    # do we encrypt correctly?
                    if check(s1, s2, level)
                        path[TWO*level] = s1
                        backtrack = search(level+1)
                        if backtrack == 0
                            set_state!(state, (s1 >> 8) | (s2 >> 2), level)
                        end
                        if backtrack < level
                            return backtrack
                        end
                    end
                end
            end
            # should return level-1 but (1) it saves a subtraction and
            # (2) it indicates failure to converge at top level
            return level
        end
        if 0 == search(1)
            state
        else
            error("no solution")
        end
    end

end


function make_cached_dfs_noro_r8{W<:Unsigned}(::Type{W}, table1, table2;
                                              initial=4, attempts=100, decay=0.1, period=1000)
    
    const DEPTH::Int = 8 * sizeof(W)
    const WIDTH::Uint = 2 * 8 + 2
    # tables of state require 6 bits offset 8 bits so generate and mask
    const SMASK::Uint = ((2 ^ 6) - 1) << 8
    const SDELTA::Uint = 1 << 8      
    # similar mask for carries
    const CMASK::Uint = ((2 ^ 6) - 1) << 2

    function solve(e)

        const N::Int = initial + 8
        known = zeros(Uint8, 3, DEPTH, N)
        const score::Vector{Int} = zeros(Int, N)
        
        function set_known(a, b, ap, bp, i)
            for level in 1:DEPTH
                known[1, level, i] = bits(a, b)
                known[3, level, i] = bits(ap, bp)
                a, b, ap, bp = a >> 1, b >> 1, ap >> 1, bp >> 1
            end
        end

        function evaluate(s1::Uint, s2::Uint, s3::Uint, level::Int, pattern::Int)
            in1::Uint = convert(Uint, known[1, level, pattern]) | s1
            out1::Uint = convert(Uint, table1[in1+ONE])
            in2::Uint = (out1 & THREE) | convert(Uint, known[2, level, pattern]) | s2
            out2::Uint = convert(Uint, table2[in2+ONE])
            k = convert(Uint, known[3, level, pattern])
            in3::Uint = (out2 & THREE) | (k & CMASK) | s3
            out3::Uint = convert(Uint, table2[in3+ONE])
            if out3 & THREE == k & THREE
                if level < DEPTH
                    known[1, level+1, pattern] = (known[1, level+1, pattern] & ~CMASK) | (out1 & CMASK)
                    known[2, level+1, pattern] = out2 & CMASK
                    known[3, level+1, pattern] = (known[3, level+1, pattern] & ~CMASK) | (out3 & CMASK)
                end
                true
            else
                false
            end
        end

        # set initial known values (no carries)
        bits(a::W, b::W) = convert(Uint8, (a & one(W)) | (b & one(W) << 1))
        for (i, (a, b)) in enumerate(chain(constants(W), spirals(W), 
                                           group(2, take(2*initial, rands(W)))))
            ap, bp = e(a, b)
            set_known(a, b, ap, bp, i)
        end

        const path::Vector{Uint} = zeros(Uint, DEPTH*3)
        function fmt_path(level)
            p = ""
            for i in 1:3*(level-1)
                p = "$p $(path[i] >> 8)"
            end
            p
        end
        function extract(ab, p, pattern)
            val::W = zero(W)
            for level in 1:DEPTH
                val = val << 1
                val = val | (known[p, level, pattern] >> (ab - 1)) & 0x1
            end
            val
        end
        function print_pattern(pattern)
            a, b = extract(1, 1, pattern), extract(3, 1, pattern)
            println("$(pad(a)) $(pad(b))  $(score[pattern])")
        end
        function print_filter()
            for pattern in 1:N
                print_pattern(pattern)
            end
        end
        function fmt_brief()
            join(map(x -> "$x", score), " ")
        end
        function update_filter(level::Int)
            # returns the level to which we need to backtrack
            perm = sortperm(score, rev=true, alg=InsertionSort)
            known, score = known[:, :, perm], score[perm]
#            print_filter()
            for i = 1:N-1
                score[i] = convert(Int, floor(score[i] * decay))
            end
            score[N] = 0
            for j in 1:attempts
                a, b = rand(W), rand(W)
                ap, bp = e(a, b)
                set_known(a, b, ap, bp, N)
                for (l, (s3, s2, s1)) in enumerate(take(level-1, group(3, path)))
                    if ! evaluate(s1, s2, s3, l, N)
                        score[N] += 1
                        return l
                    end
                end
            end
#            print_pattern(N)
            level
        end

        function check(s1::Uint, s2::Uint, s3::Uint, level::Int)
            for i in 1:N
                if ! evaluate(s1, s2, s3, level, i)
                    score[i] += 1
                    return false
                end
            end
            true
        end

        counter::Uint = ZERO
        const state::State{W} = State(EIGHT, zeros(W, WIDTH), rotate=NoRotation)
        function search(level::Int)
            # returns the level to which we must backtrack, or 0 on success
            backtrack::Int = 0
            counter = counter + ONE
            if counter == period || level > DEPTH
#                println("$level $(fmt_path(level))")
                print("$level $(fmt_path(level))    $(fmt_brief()) /")
                counter = ZERO
                # filter before exiting when level > DEPTH to run final check
                backtrack = update_filter(level)
                println(" $(fmt_brief())")
                if backtrack < level
                    return backtrack
                elseif level > DEPTH
                    return 0
                end
            end
            # if we are not backtracking, search next level
            for s3 in ZERO:SDELTA:SMASK
                path[THREE*level-TWO] = s3
                for s2 in ZERO:SDELTA:SMASK
                    path[THREE*level-ONE] = s2
                    for s1 in ZERO:SDELTA:SMASK
                        # do we encrypt correctly?
                        if check(s1, s2, s3, level)
                            path[THREE*level] = s1
                            backtrack = search(level+1)
                            if backtrack == 0
                                set_state!(state, (s1 >> 8) | (s2 >> 2) | (s3 << 4), level)
                            end
                            if backtrack < level
                                return backtrack
                            end
                        end
                    end
                end
            end
            # should return level-1 but (1) it saves a subtraction and
            # (2) it indicates failure to converge at top level
            return level
        end
        if 0 == search(1)
            state
        else
            error("no solution")
        end
    end

end


# ---- ripple diagrams


type Trace{W<:Unsigned}
    header::String
    value::Union(W, Nothing)
end

Trace{W<:Unsigned}(header::String, ::Type{W}) = Trace{W}(header, nothing)

Base.isequal{W<:Unsigned}(t1::Trace{W}, t2::Trace{W}) = 
isequal(t1.header, t2.header) && isequal(t1.value, t2.value)


function encrypt{W<:Unsigned, R<:Rotation}(s::State{W, R}, a::W, b::W,
    trace::Vector{Trace{W}}; both=false)

    blank = Trace(" ", W)
    space() = push!(trace, blank)

    function push_maybe(trace, t)
        if length(trace) > 1 && trace[end] == blank && trace[end-1] == t
            pop!(trace)
        else
            push!(trace, t)
        end
    end

    function apply(f, op::String, arg1::W, head1::Union(String, Nothing), 
                   arg2::W, head2::String, head3::String)
        
        # re-use previous if possible for more compact display
        push_maybe(trace, Trace(head1, arg1))
        push!(trace, Trace(op, W))
        push!(trace, Trace(head2, arg2))
        result::W = f(arg1, arg2)
        space()
        push!(trace, Trace(head3, result))
        space()
        result
    end

    add(arg1::W, head1::String, arg2::W, head2::String) =
    apply(+, "+", arg1, head1, arg2, head2, head1)

    xor(arg1::W, head1::String, arg2::W, head2::String, head3::String) =
    apply($, "x", arg1, head1, arg2, head2, head3)

    rot(::Type{NoRotation}, arg1::W, head1::String, arg2::W, head2::String, i::Unsigned) =
    arg1

    function rot(::Type{RoundRotation}, arg1::W, head1::String, arg2::W, head2::String, i::Unsigned)
        push_maybe(trace, Trace(head1, arg1))
        push!(trace, Trace("^$(i)", W))
        result::W = rotatel(arg1, i)
        push!(trace, Trace(head1, result))
        space()
        result
    end

    rot(::Type{FullRotation}, arg1::W, head1::String, arg2::W, head2::String, i::Unsigned) =
    apply(rotatel, "<", arg1, head1, arg2, head2, head1)

    push!(trace, Trace("b", b))
    space()

    a::W = add(a, "a", s.s[1], "s0")
    b::W = both ? add(b, "b", s.s[2], "s1") : b + s.s[2]

    for i in 0x1:s.r

        a = xor(b, "b", a, "a", "a")
        a = rot(s.rotate, a, "a", b, "b", i)
        a = add(a, "a", s.s[2i+1], "s$(2i)")

        if both
            b = xor(a, "a", b, "b", "b")
            b = rot(s.rotate, b, "b", a, "a", i)
            b = add(b, "b", s.s[2i+2], "s$(2i+1)")
        else
            b = a $ b
            b = rotatel(s.rotate, b, a, i)
            b = b + s.s[2i+2]
        end

    end

    push_maybe(trace, Trace("a", a))

    a, b
end

function format_string!(chars, text)
    for (i, c) in enumerate(text)
        chars[i] = c
    end
end

function format{W<:Unsigned}(trace::Vector{Trace{W}}; 
                             title=true, range=1:0)
    if range.len < 1
        range = 1:8*sizeof(W)
    end
    header = title ? 1 + maximum(map(t -> length(t.header), trace)) : 0
    height = header + range.len
    width = 1 + length(trace)
    chars = Array(Char, width, height)
    fill!(chars, ' ')
    fill!(slice(chars, width, 1:height), '\n')
    for i in 1:width-1
        if trace[i].value != nothing
            format_string!(slice(chars, i, header+1:height), 
                           bits(trace[i].value)[range])
        else
            fill!(slice(chars, i, header+1:8:height), trace[i].header[1])
        end
        if title
            format_string!(slice(chars, i, 1:header), trace[i].header)
        end
    end
    chars
end

function trace{W<:Unsigned}(state::State{W}, a::W, b::W;
                            title=true, range=1:0, both=false)
    t = Array(Trace{W}, 0)
    encrypt(state, a, b, t, both=both)
    chars = format(t, title=title, range=range)
    return string(reshape(chars, length(chars))...)
end

function diff(c1, c2)
    w, h = size(c1)
    @assert (w, h) == size(c2)
    d = Array(Char, w, h)
    fill!(d, ' ')
    fill!(slice(d, w, 1:h), '\n')
    for i in 1:w
        for j in 1:h
            if c1[i, j] != c2[i, j]
                d[i, j] = c2[i, j]
            end
        end
    end
    d
end

function print_delta{W<:Unsigned}(state::State{W}, ab::Vector{(W,W)};
                                  range=1:0, both=false, chain=false)
    t = Array(Trace{W}, 0)
    a, b = ab[1]
    encrypt(state, a, b, t, both=both)
    chars = format(t, title=true, range=range)
    println()
    println(string(reshape(chars, length(chars))...))

    reference = format(t, title=false, range=range)
    for (a, b) in ab[2:end]
        u = Array(Trace{W}, 0)
        encrypt(state, a, b, u, both=both)
        update = format(u, title=false, range=range)
        d = diff(reference, update)
        println(string(reshape(d, length(d))...))
        if chain
            reference = update
        end
    end
end

function prove_carry{W<:Unsigned}(::Type{W}, r::Uint8, s, nmax)

    # the idea here was that the final addition leaked information via
    # the carry.  but it doesn't.

    n_strong, n_weak = 0, 0
    for i in 1:nmax
        state = State(W, r, collect(Uint8, take(s, rands(Uint8))), 
                      rotate=NoRotation)
        a, b = collect(W, take(2, rands(W)))
        ap, bp = encrypt(state, a, b)
        a1, _ = encrypt(state, a $ one(W), b)
        a2, _ = encrypt(state, a $ one(W), b $ (one(W) << 1))
#        println("$a $ap $a1 $a2")
        if 0 == state.s[2r+1] & 0x1
            # if bit 0 of the final state added to a is zero then we will
            # one of a1 or a2 will not have a carry into bit 1
            if 0 != (ap $ a1) & 0x2 && 0 != (ap $ a2) & 0x2
#                println("\ncounter-example - both have carries")
#                print_delta(state, [(a, b), (a $ one(W), b), 
#                                    (a $ one(W), b $ (one(W) << 1))])
            else
                n_strong += 1
            end
        else
            # if bit 0 is 1 then a1 will always have a carry
            if 0 == (ap $ a1) & 0x2
#                println("\ncounter-example - no carry")
#                print_delta(state, [(a, b), (a $ one(W), b)])
            else
                n_weak += 1
            end
        end
    end
    println("carry count: $n_strong / $n_weak")
end

function prove_nonlinear{W<:Unsigned}(::Type{W}, r::Uint8, k, nmax)
    n_add, n_xor = 0, 0
    for i in 1:nmax
        state = State(W, r, collect(Uint8, take(k, rands(Uint8))), 
                      rotate=NoRotation)
        a, b, c, d = collect(W, take(4, rands(W)))
        p, q = encrypt(state, convert(W, a+c), convert(W, b+d))
        rs1 = encrypt(state, a, b)
        rs2 = encrypt(state, c, d)
        r = convert(W, rs1[1] + rs2[1])
        s = convert(W, rs1[2] + rs2[2])
        if p == r || q == s
            n_add += 1
            if p == r
#                println("add $(bits(p))   $(bits(a)) $(bits(c))")
            end
            if q == s
#                println("add $(bits(q))   $(bits(b)) $(bits(d))")
            end
        end
        p, q = encrypt(state, a$c, b$d)
        rs1 = encrypt(state, a, b)
        rs2 = encrypt(state, c, d)
        r::W = rs1[1] $ rs2[1]
        s::W = rs1[2] $ rs2[2]
        if p == r || q == s
            n_xor += 1
            if p == r
#                println("xor $(bits(p))   $(bits(a)) $(bits(c))")
            end
            if q == s
#                println("xor $(bits(q))   $(bits(b)) $(bits(d))")
            end
        end        
    end
    println("linear count: $n_add / $n_xor")
end


# ---- local search

function make_search_roundro{W<:Unsigned}(::Type{W}, r; retry=8, bias=3)

    # even with rotation, a single input bit only affects a limited
    # range of output bits (for sufficiently wide half-blocks and 
    # sufficiently few rounds).  so we can search through the input
    # bits that affect a single output (only).

    function solve(ctext, e)

        n_bits = 8 * sizeof(W)
        l, o = one(W), zero(W)
        offset = convert(Uint, r*(r+1)/2)

        Task() do

            for (c, d) in group(2, pack(W, ctext))

                width, searching, shift = 1, true, zero(Uint)
                a::W, b::W = o, o

                while searching && width < n_bits

                    if shift % (retry * n_bits) == 0
                        width += 1
                        println("$width")
                        n::W = convert(W, 2 ^ width - 1)
                        in_mask::W = (l << width) - l
                        out_mask::W = rotatel(in_mask, offset)
                        in_bit::W = l
                        out_bit::W = rotatel(in_bit, offset)
                    end

                    best, a2::W, b2::W = 0, o, o
                    for i::W in o:n
                        a1::W = (a & ~in_mask) | rotatel(i, shift)
                        for j::W in o:n
                            b1::W = (b & ~in_mask) | rotatel(j, shift)
                            c1::W, d1::W = e(a1, b1)
                            score = (count_zeros((c1 $ c) & out_mask) +
                                     count_zeros((d1 $ d) & out_mask))
#                                     ((c1 $ c) & out_mask == 0 ? bias : 0) +
#                                     ((d1 $ d) & out_mask == 0 ? bias : 0))
                            if score > best
                                a2, b2 = a1, b1
                                best = score
                            end
                        end
                    end
                    a, b = (a & ~in_bit) | (a2 & in_bit), (b & ~in_bit) | (b2 & in_bit)
                    in_mask, in_bit = rotatel(in_mask, l), rotatel(in_bit, l)
                    out_mask, out_bit = rotatel(out_mask, l), rotatel(out_bit, l)
                    c2, d2 = e(a, b)
                    searching = !(c2 == c && d2 == d)
                    shift += one(Uint)

                    if !searching
                        println("$shift / $width")
                    end
                end

                produce_from(unpack(W, a))
                produce_from(unpack(W, b))
            end
        end
    end

end


# to improve local search we need a more accurate idea of what output bits
# are affected by what input

function tabulate_influence{W<:Unsigned}(::Type{W}, r, e; n=100)
    width = 8 * sizeof(W)
    # output bit posn -> input bit posn -> number of times output changed
    # (bits are 1-indexed)
    influence::Array{Dict{Int,Int}} = [(Int=>Int)[] for _ in 1:width]
    for _ in 1:n
        a, b = take(2, rands(W))
        c, d = e(a, b)
        for input in 1:width
            for x in 1:3
                bit = one(W) << (input-1)
                a1 = x & 1 != 0 ? a : a $ bit
                b1 = x & 2 != 0 ? b : b $ bit
                for changed in map(x -> x[1] $ x[2], zip(e(a1, b1), (c, d)))
                    for output in 1:width
                        if changed & 1 != 0
                            m = influence[input]
                            m[output] = get(m, output, 0) + 1
                        end
                        changed = changed >> 1
                    end
                end
            end
        end
    end
    influence
end


function print_influence(influence, r)
    width = length(influence)
    offset = convert(Int, r * (r+1) / 2)
    for input in 1:width
        @printf("%2d ", input-1)
        m = influence[input]
        biggest = maximum(values(m))
        for output in 1:width
            if output % width == (input + offset) % width
                print(">")
            end
            value = get(m, output, 0)
            if value == 0
                print("-")
            elseif value == biggest
                print("^")
            else
                @printf("%d", floor(10 * value / biggest))
            end
            if output % width == (input + offset) % width
                print("<")
            end
        end
        print("\n")
    end
end



# ---- validate solutions

make_keygen(w, r, k; rotate=FullRotation) = 
() -> State(w, r, collect(Uint8, take(k, rands(Uint8))), rotate=rotate)
fake_keygen(w, r, k; rotate=FullRotation) = 
() -> State(w, r, collect(Uint8, take(k, constant(0x0))), rotate=rotate)

function solutions()
    ptext_from_encrypt(3, make_search_roundro(Uint32, 6), 
                       make_keygen(Uint32, 0x6, 0x2, rotate=RoundRotation),
                       k -> p -> encrypt(k, p), 32,
                       eq=same_ptext(),
                       encrypt2=k -> (a, b) -> encrypt(k, a, b))
    return
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
end


# ---- tests

function test_trace()
    @assert Trace{Uint8}("a", nothing) == Trace{Uint8}("a", nothing)
    @assert Trace{Uint8}("a", 0x1) == Trace{Uint8}("a", 0x1)
    @assert Trace{Uint8}("a", 0x2) != Trace{Uint8}("a", 0x1)
    @assert Trace{Uint8}("a", 0x1) != Trace{Uint8}("b", 0x1)
    println(trace(State(Uint16, 0x3, zeros(Uint8, 16), rotate=NoRotation), 
                  0x0000, 0x0000))
    print_delta(State(Uint8, 0x3, zeros(Uint8, 16), rotate=NoRotation), 
                [(0x00, 0x00), (0x01, 0x00), (0x01, 0x02)])
    print_delta(State(Uint8, 0x3, zeros(Uint8, 16), rotate=RoundRotation), 
                [(0x00, 0x00), 
                 (0x01, 0x00), (0x03, 0x00), (0x07, 0x00), (0x0f, 0x00), 
                 (0x1f, 0x00), (0x3f, 0x00), (0x7f, 0x00), (0xff, 0x00)], 
                both=true, chain=true)
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

function test_8()
    # just checking the code runs (correct values unknown)
    a, b = encrypt(State(Uint8, 0x0c, zeros(Uint8, 16)), 0x00, 0x00)
    @assert a == 0xa6 a
    @assert b == 0xea b
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
end

function test_cached_dfs_r5(table1, table2)
#    s = State(FIVE, collect(Uint32, take(12, rands(Uint32))), rotate=NoRotation)
    s = State(FIVE, zeros(Uint32, 12), rotate=NoRotation)
    s.s[1] = convert(Uint32, -1)
    s.s[2] = 0x55555555
    s.s[3] = convert(Uint32, -1)
    solve = make_cached_dfs_noro_r5(Uint32, table1, table2)
    s1 = solve((a, b) -> encrypt(s, a, b))
    println("\n$s\n$s1\n")
    @assert same_ctext(100, encrypt)(s, s1)
#    solve((a, b) -> encrypt(s, a, b))
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
    for (a, b) in [(0, 0), (-1, -1), (0, -1), (-1, 0)]
        a, b = convert(Uint32, a), convert(Uint32, b)
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
end

function test_influence{W<:Unsigned}(::Type{W}, r; k=16)
    s = State(W, r, collect(Uint8, take(k, rands(Uint8))), rotate=RoundRotation)
    e = (a, b) -> encrypt(s, a, b)
    print_influence(tabulate_influence(W, r, e), r)
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
end


tests()
solutions()

end
