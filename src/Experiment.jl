
module Experiment


function xor_diff_stats()
    # for RC5, one round, no rotations, we have ((X-C) $ K) - ((Y-C) $ K)
    # and would like to find K, given the ability to choose X and Y.
    # it seems like one way to do that is to choose X randomly, flip
    # a bit for Y, and look at the stats for the difference.
    n = 100
    results = Array(Uint8, 2, n)
    for j = 1:2
        for i = 1:n
            k = rand(Uint8)
            if j == 1
                k = k & 0xef
            else
                k = k | 0x10
            end
            c = rand(Uint8)
            x = rand(Uint8)
            # xor doesn't work below (symmetric results), but subtraction
            # or addition do, nicely.
            y::Uint8 = x + 16
            d::Uint8 = ((x-c) $ k) - ((y-c) $ k)
            println("$x $y $c $k $d")
            results[j, i] = d
        end
    end
    println(results)
end

xor_diff_stats()

end
