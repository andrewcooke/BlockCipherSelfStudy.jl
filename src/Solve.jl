
module Solve
export solve_known_cipher, rands

using Tasks

function solve_known_cipher(n, solve, keygen, encrypt; eq= ==)
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

rands{T<:Integer}(::Type{T}) = repeat(() -> rand(T))

end

