
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
    const ALL_ONES::W, ALL_ZEROS::W = typemax(W), zero(W)
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


function test_cached_dfs_r5(table1, table2)
#    s = State(FIVE, collect(Uint32, take(12, rands(Uint32))), rotate=NoRotation)
    s = State(FIVE, zeros(Uint32, 12), rotate=NoRotation)
    s.s[1] = typemax(Uint32)
    s.s[2] = 0x55555555
    s.s[3] = typemax(Uint32)
    solve = make_cached_dfs_noro_r5(Uint32, table1, table2)
    s1 = solve((a, b) -> encrypt(s, a, b))
    println("\n$s\n$s1\n")
    @assert same_ctext(100, encrypt)(s, s1)
#    solve((a, b) -> encrypt(s, a, b))
    println("test_cached_dfs ok")
end
