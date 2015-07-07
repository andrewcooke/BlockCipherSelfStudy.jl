
# ---- 1 round no rotation solution

function r1_noro{W<:Unsigned}(a::W, b::W, s1::W, s2::W, s3::W, s4::W)
    a = a + s1
    b = b + s2
    a = (a $ b) + s3
    b = (b $ a) + s4
    a, b
end

function make_solve_r1_noro{W<:Unsigned}(::Type{W})
    function solve(e)
        # a' = ((a + s[1]) $ (b + s[2])) + s[3]
        # a0'-a1' = ((a0 + s[1]) $ (b0 + s[2])) - ((a1 + s[1]) $ (b1 + s[2]))
        # choose b0 == b1 = 0
        # a0'-a1' = ((a0 + s[1]) $ s[2]) - ((a1 + s[1]) $ s[2])
        # choose a0 and a1 to be same except for 1 bit - can get bit for s[2]
        # except for msb; see Experiment.jl
        k::W = 0x0
        m::W = 0x0
        # find bit using differences (see Experiment.jl)
        for b = 0:(8*sizeof(W)-1)
            m = m == 0 ? 1 : m << 1
            while true
                a0::W = rand(W)
                a1::W = a0 - m  # minus here
                ap0, _ = e(a0, convert(W, 0x0))
                ap1, _ = e(a1, convert(W, 0x0))
                d = convert(Int64, ap0) - convert(Int64, ap1)
                if d == m  # subtract and find, so bit zero
 #                   println("bit $b of s2 0: $(pad(k))")
                    break
                end
                a1 = a0 + m  # plus here
                ap0, _ = e(a0, convert(W, 0x0))
                ap1, _ = e(a1, convert(W, 0x0))
                d = convert(Int64, ap0) - convert(Int64, ap1)
                if d == m  # add and find, so bit one
                    k = k+m
#                    println("bit $b of s2 1: $(pad(k))")
                    break
                end
            end
        end
        # at this point we know k (s[2]) except for msb (m)
        for s2::W in (k, k+m)
            # if we know s[2], set b0+s[2]=0, b1+s[2]=0xf..f, a0=0, a1=0
            # a0'-a1' = ((a0+s[1]) $ (b0+s[2])) - ((a1+s[1]) $ (b1+s[2]))
            #         = (s[1] - (s[1] $ 0xf..f))
            #         = s[1] - (-s[1]-1)
            ap0, _ = e(zero(W), -convert(W, s2))
            ap1, _ = e(zero(W), -convert(W, s2)-one(W))
#            println("a0' $(pad(ap0))  a1' $(pad(ap1))")
            s1l7::W = convert(W, ap0 - ap1 - 1) >> 1  # don't know top bit
            for s1::W in (s1l7, s1l7+0x80)
                s3::W = ap0 - s1
		u::W, v::W = rand(W), rand(W)
                up::W, vp::W = e(u, v)
		s4::W = convert(W, vp - (convert(W, v + s2) $ up))
#                println("if s2=$(pad(s2)) and s1=$(pad(s1)) then s3=$(pad(s3)) and s4=$(pad(s4))")
                # check if the current s1,2,3 are ok
                i, ok = 0, true
                while ok && i < 10
		    u, v = rand(W), rand(W)
                    up, vp = e(u, v)
                    upp::W, vpp::W = r1_noro(u, v, s1, s2, s3, s4)
#		    println("$(pad(up)) $(pad(upp)) $(pad(vp)) $(pad(vpp))")
                    ok = up == upp && vp == vpp
		    i = i+1
		end
		if ok
                    # pack final state
                    s = State(ONE, W[s1, s2, s3, s4], rotate=NoRotation)
		    println("result $s")
                    return s
		else
		    println("bad check")
                end
            end
        end
        error("failed to find solution")
    end
end

