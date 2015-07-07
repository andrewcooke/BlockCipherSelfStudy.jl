
using ..GA

# genetic algorithm to derive state

# the "real" score is the float; the ints are to show how many of each bit
# we have encoded correctly and to assess completness (and so target mutation)
@compat typealias Score Tuple{Float64, Vector{Int}}

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


