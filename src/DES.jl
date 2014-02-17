
module DES
using Tasks, Solve

abstract SBox
type WithSBox <: SBox end
type WithoutSBox <: SBox end

immutable State{S<:SBox}
    r::Uint8
    key::Uint64
    k::Array{Uint64}  # lowest 48 bits
    sbox::Type{S}
end

State{S<:SBox}(key::Uint64; r::Uint8=0x10, sbox::Type{S}=WithSBox) = 
State{S}(r, key, expand_key(r, key), sbox)

function expand_key(r::Uint8, key::Uint64)
    println(bin(key))
    k56 = permute_bits(key, 64, 56,
                       [57, 49, 41, 33, 25, 17,  9,  1, 58, 50, 42, 34, 26, 18,
                        10,  2, 59, 51, 43, 35, 27, 19, 11,  3, 60, 52, 44, 36,
                        63, 55, 47, 39, 31, 23, 15,  7, 62, 54, 46, 38, 30, 22,
                        14,  6, 61, 53, 45, 37, 29, 21, 13,  5, 28, 20, 12,  4])
    println(bin(k56))
    c, d = split_28(k56)
    k = Array(Uint64, 0)
    for n in take(r, chain([1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1]))
        for _ in 1:n
            c, d = rotatel_28(c), rotatel_28(d)
        end
        k56 = join_28(c, d)
        println(bin(k56))
        push!(k, permute_bits(k56, 56, 48,
                              [14, 17, 11, 24,  1,  5,  3, 28, 15,  6, 21, 10,
                               23, 19, 12,  4, 26,  8, 16,  7, 27, 20, 13,  2,
                               41, 52, 31, 37, 47, 55, 30, 40, 51, 45, 33, 48,
                               44, 49, 39, 56, 34, 53, 46, 42, 50, 36, 29, 32]))
    end
    k
end

# perm is 1-based index from msb(!)
function permute_bits{U<:Unsigned}(in::U, from, to, perm)
    out::U = zero(U)
    mask::U = one(U) << (to - 1)
    for p in perm
        if in & (one(U) << (from - p)) != 0
            out = out | mask
        end
        mask = mask >>> 1
    end
    out
end
permute_bits{U<:Unsigned}(in::U, from, perm) = permute_bits(in, from, from, perm)
permute_bits{U<:Unsigned}(in::U, perm) = permute_bits(in, 8*sizeof(U), perm)

const MASK_28 = (one(Uint64) << 28) - 1
 
function split_28(k56::Uint64)
    k56 >> 28 & MASK_28, k56 & MASK_28
end

function join_28(c::Uint64, d::Uint64)
    c << 28 | d
end

function rotatel_28(n::Uint64)
    MASK_28 & (n << 1 | n >>> 27)
end


function test_permutation()
    for r1 in take(10, rands(Uint8))
        r2 = permute_bits(r1, [1,2,3,4,5,6,7,8])
        @assert r1 == r2
    end
    r1 = permute_bits(0b11000000, [2,3,4,5,6,7,8,1])
    @assert r1 == 0b10000001
end

function test_schedule()
    # http://www.herongyang.com/Cryptography/DES-Illustration-DES-Key-Schedule-Output.html
    s = State(0b0001001100110100010101110111100110011011101111001101111111110001)
    @assert s.k[1] == 0b000110110000001011101111111111000111000001110010
    @assert s.k[16] == 0b110010110011110110001011000011100001011111110101
end

function tests()
    test_permutation()
    test_schedule()
end

tests()

end
