
module Blocks
export pack, unpack, group, ungroup, pad, produce_from

function pack{W<:Unsigned}(::Type{W}, bytes; little=true)
    # this is little-endian by default
    block::W = 0x0
    i = 0
    Task() do
        for b::W in bytes
            if little
                block = block | b << 8 * i
            else
                block = block << 8 | b
            end
            i = i + 1
            if i == sizeof(W)
                produce(block)
                block = 0x0
                i = 0
            end
        end
    end
end

function unpack{W<:Unsigned}(::Type{W}, blocks; little=true)
    Task() do
        for block in blocks
            for i in 1:sizeof(W)
                if little
                    produce(convert(Uint8, block & 0xff))
                    block = block >> 8
                else
                    produce(convert(Uint8, (block >> 8 * (sizeof(W) - i)) & 0xff))
                end
            end
        end
    end
end
unpack{W<:Unsigned}(a::Array{W,1}) = unpack(W, a)

function group(n, seq)
    tmp = cell(n)
    Task() do
        i = 1
        for s in seq
            tmp[i] = s
            if i == n
                produce(tuple(tmp...))
                i = 1
            else
                i = i + 1
            end
        end
    end
end

function ungroup(seq)
    Task() do
        for subseq in seq
            for value in subseq
                produce(value)
            end
        end
    end
end

function pad{W<:Unsigned}(n::W)
    hex(n, 2 * sizeof(W))
end

function produce_from(seq)
    for s in seq
        produce(s)
    end
end


function test_pack()
    b = collect(unpack(Uint32, pack(Uint32, b"123456789")))
    @assert b == b"12345678" b
    b = collect(unpack(Uint32, pack(Uint32, b"123456789", little=false), little=false))
    @assert b == b"12345678" b
    @assert 0x1234 == consume(pack(Uint16, hex2bytes("3412")))
    @assert 0x1234 == consume(pack(Uint16, hex2bytes("1234"), little=false))
end

function tests()
    test_pack()
end

#tests()

end

