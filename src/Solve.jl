
module Solve
export key_from_encrypt, ptext_from_encrypt, rands, same_ctext, same_ptext

using Tasks, Blocks

function key_from_encrypt(n, solve, keygen, encrypt; eq= ==)
    for i = 1:n
        k1 = keygen()
        println("target $k1")
        k2 = solve(encrypt(k1))
        ok = eq(k1, k2)
        println("$i: $k2 $ok")
        @assert ok
    end
end

function ptext_from_encrypt(n, solve, keygen, encrypt, len; 
                            eq= ==, encrypt2=nothing)
    for i = 1:n
        k = keygen()
        e1 = encrypt(k)
        e2 = encrypt2 == nothing ? e1 : encrypt2(k)
        p1 = collect(Uint8, take(len, rands(Uint8)))
        println("target $(bytes2hex(p1))")
        c = e1(p1)
        p2 = collect(Uint8, solve(c, e2))
        ok = eq(p1, p2)
        println("$i: $(bytes2hex(p2)) $ok")
        @assert ok
    end
end

rands{T<:Integer}(::Type{T}) = repeat(() -> rand(T))

function same_ctext(n, encrypt)
    function eq(k1, k2)
        p = collect(Uint8, take(n, rands(Uint8)))
        c1 = collect(Uint8, encrypt(k1, p))
        c2 = collect(Uint8, encrypt(k2, p))
        c1 == c2
    end
end

function same_ptext{W<:Unsigned}(::Type{W}, nbits)
    function eq(p1, p2)
        m::W = 2^nbits - 1
        ok = true
        for (a::W, b::W) in zip(pack(W, p1), pack(W, p2))
#            println("$(pad(a))/$(pad(a & m)) $(pad(b))/$(pad(b & m))")
            ok = ok && a & m == b & m
        end
        ok
    end
end

same_ptext(W) = same_ptext(W, sizeof(W))
same_ptext() = same_ptext(Uint8)

end
