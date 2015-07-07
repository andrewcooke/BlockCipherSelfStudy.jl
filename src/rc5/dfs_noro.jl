
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

function test_bits{W<:Unsigned}(ptext::Vector{Tuple{W,W}}, ctext::Vector{Tuple{W,W}}, state::State{W}, level::Uint)
    mask::W = (one(W) << level) - one(W)
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
        ptext = collect(Tuple{W, W}, group(2, take(2*len, rands(W))))
        ctext = Tuple{W,W}[e(a, b) for (a, b) in ptext]
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
