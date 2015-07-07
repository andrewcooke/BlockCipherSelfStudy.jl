
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
