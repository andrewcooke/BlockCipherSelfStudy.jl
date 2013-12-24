
module Solve
export from_known_ptext, from_known_state, rands, same_ctext

using Tasks

function from_known_ptext(n, solve, keygen, encrypt; eq= ==)
    println(solve)
    for i = 1:n
        k1 = keygen()
        println("target $k1")
        e = plain -> encrypt(k1, plain)
        tic()
        k2 = solve(e)
        t = toq()
        @printf("%d: %s %s\n", i, k1, eq(k1, k2))
    end
end

function from_known_state(n, solve, keygen, test)
    # this isn't as rigorous as the test above - we pass the state 
    # explicitly - but it can be more efficient.
    println(solve)
    for i = 1:n
        k1 = keygen()
        println("target $k1")
        tic()
        oracle = solve(k1)
        t = toq()
        @printf("%d: %s %s\n", i, k1, test(k1, oracle))
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

end
