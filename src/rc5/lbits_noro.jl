
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
