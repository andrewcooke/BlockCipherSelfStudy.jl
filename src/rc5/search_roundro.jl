
# ---- local search

function common_bits{W<:Unsigned}(a::W, b::W, mask::W)
    return count_zeros(((a $ b) & mask) | ~mask)
end

function make_search_roundro{W<:Unsigned}(::Type{W}, r; retry=2, bias=4)

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

                width, searching, shift = 0, true, zero(Uint)
                a::W, b::W = o, o
                c2, d2 = e(a, b)

                while searching && width < n_bits

                    # in_bit is the top-most bit of the range being searched;
                    # it is rotated to out_bit.  in_mask and out_mask are the
                    # enire range.

                    if shift % (retry * n_bits) == 0
                        width += 1
                        println("$width")
                        n::W = convert(W, 2 ^ width - 1)
                        in_mask::W = (l << width) - l
                        out_mask::W = rotatel(in_mask, offset)
                        in_bit::W = l << (width - 1)
                        out_bit::W = rotatel(in_bit, offset)
                    end

                    # search wherever the target bit is incorrect

                    if c2 & out_bit != c & out_bit || d2 & out_bit != d & out_bit

                        best, a2::W, b2::W, escape = 0, o, o, false
                    
                        for i::W in o:n
                            a1::W = (a & ~in_mask) | rotatel(i, shift)
                            for j::W in o:n
                                b1::W = (b & ~in_mask) | rotatel(j, shift)
                                c1::W, d1::W = e(a1, b1)
                                score = (bias * bias * bias * common_bits(c1, c, out_bit) +
                                         bias * bias * bias * common_bits(d1, d, out_bit) +
                                         bias * bias * common_bits(c1, c, out_mask & ~out_bit) +
                                         bias * bias * common_bits(d1, d, out_mask & ~out_bit) +
                                         bias * common_bits(a1, a, in_mask) +
                                         bias * common_bits(b1, b, in_mask) +
                                         common_bits(c1, c, ~out_mask) + 
                                         common_bits(d1, d, ~out_mask))
                                if score > best
                                    a2, b2 = a1, b1
                                    best = score
                                end
                            end
                        end
#                        a, b = (a & ~in_bit) | (a2 & in_bit), (b & ~in_bit) | (b2 & in_bit)
#                        a, b = (a & ~in_mask) | (a2 & in_mask), (b & ~in_mask) | (b2 & in_mask)
                        println()
                        println("a:$(bin(a, n_bits)) b:$(bin(b, n_bits))")
                        println("2:$(bin(a2, n_bits)) 2:$(bin(b2, n_bits))  $(best)")
                        println("  $(bin(in_mask, n_bits))   $(bin(in_mask, n_bits))  $(shift % n_bits)")
                        println("  $(bin(in_bit, n_bits))   $(bin(in_bit, n_bits))")
                        a, b = a2, b2
                        c2, d2 = e(a, b)
                        println("c:$(bin(c, n_bits)) d:$(bin(d, n_bits))")
                        println("2:$(bin(c2, n_bits)) 2:$(bin(d2, n_bits))")
                        println("  $(bin(out_mask, n_bits))   $(bin(out_mask, n_bits))  $(offset)")
                        println("  $(bin(out_bit, n_bits))   $(bin(out_bit, n_bits))")
                    end

                    in_mask, in_bit = rotatel(in_mask, l), rotatel(in_bit, l)
                    out_mask, out_bit = rotatel(out_mask, l), rotatel(out_bit, l)
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
    influence::Array{Dict{Int,Int}} = [Dict{Int,Int}() for _ in 1:width]
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


function test_influence{W<:Unsigned}(::Type{W}, r; k=16)
    s = State(W, r, collect(Uint8, take(k, rands(Uint8))), rotate=RoundRotation)
    e = (a, b) -> encrypt(s, a, b)
    print_influence(tabulate_influence(W, r, e), r)
    println("test_influence ok")
end

function test_common_bits()
    @assert 1 == common_bits(0x000000001, 0x000000001, 0x000000001)
    @assert 2 == common_bits(0x000000001, 0x000000001, 0x000000011)
    @assert 1 == common_bits(0x000000011, 0x000000001, 0x000000011)
    @assert 0 == common_bits(0x000000010, 0x000000001, 0x000000011)
    println("test_common_bits ok")
end

function test_local_search(r)
    s = State(Uint32, r, zeros(Uint8, 8), rotate=RoundRotation)
    e = (a, b) -> encrypt(s, a, b)
    search = make_search_roundro(Uint32, r)
    ptext = b"hello world xxxx"  # exact number of blocks
    ctext = encrypt(s, ptext)
    result = collect(Uint8, search(ctext, e))
    @assert result == ptext
    println("test_local_search ok")
end
