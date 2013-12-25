
module Blocks
export pack, unpack, group, pad

function pack{W<:Unsigned}(::Type{W}, bytes)
    block::W = 0x0
    i = 0
    Task() do
        for b::W in bytes
            block = block | b << 8i
            i = i + 1
            if i == sizeof(W)
                produce(block)
                block = 0x0
                i = 0
            end
        end
    end
end

function unpack{W<:Unsigned}(::Type{W}, blocks)
    Task() do
        for block in blocks
            for i in 1:sizeof(W)
                produce(convert(Uint8, block & 0xff))
                block = block >> 8
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

function pad{W<:Unsigned}(n::W)
    s = @sprintf("%x", n)
    while length(s) < 2 * sizeof(W)
        s = "0$s"
    end
    s
end


function test_pack()
    b = collect(unpack(Uint32, pack(Uint32, b"123456789")))
    @assert b == b"12345678" b
end

function tests()
    test_pack()
end

#tests()

end

