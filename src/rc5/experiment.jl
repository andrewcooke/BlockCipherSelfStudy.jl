
function xor_diff_stats()
    # for RC5, one round, no rotations, we have ((X+C) $ K) - ((Y+C) $ K)
    # and would like to find K, given the ability to choose X and Y.
    # it seems like one way to do that is to choose X randomly, flip
    # a bit for Y, and look at the stats for the difference.
    n = 8
    k::Uint8 = rand(Uint8)
    c::Uint8 = rand(Uint8)
    @printf("k = %d, c = %d\n", k, c)
    for b in 0:7
        println("bit $b")
        m::Uint8 = 1 << b
        for j = 1:2
            @printf("%d in k\n", (j-1)) 
            for l = 1:2
                print(l == 1 ? "+ " : "- ")
                results = Array(Int64, n)
                for i = 1:n
		    kk::Uint8
                    if j == 1
                        kk = k & ~m
                    else
                        kk = k | m
                    end
                    x::Uint8 = rand(Uint8)
                    # xor doesn't work below (symmetric results).
                    # subtraction or addition works fine.
                    y::Uint8
                    if l == 1
                        y = x + m
                    else
                        y = x - m
                    end
                    d = convert(Int64, convert(Uint8, x+c) $ kk) - convert(Int64, convert(Uint8, y+c) $ kk)
                    # @printf("%x x%x y%x x-y%d c%x k%x d%x\n", m, x, y, convert(Int, x)-convert(Int, y), c, kk, d)
                    results[i] = d
                end
                print(results')
            end
        end
    end
end

xor_diff_stats()
