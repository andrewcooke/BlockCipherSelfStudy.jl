
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


const KEY = [57, 49, 41, 33, 25, 17,  9,  1, 58, 50, 42, 34, 26, 18,
             10,  2, 59, 51, 43, 35, 27, 19, 11,  3, 60, 52, 44, 36,
             63, 55, 47, 39, 31, 23, 15,  7, 62, 54, 46, 38, 30, 22,
             14,  6, 61, 53, 45, 37, 29, 21, 13,  5, 28, 20, 12,  4]

const COMPRESSION = [14, 17, 11, 24,  1,  5,  3, 28, 15,  6, 21, 10,
                     23, 19, 12,  4, 26,  8, 16,  7, 27, 20, 13,  2,
                     41, 52, 31, 37, 47, 55, 30, 40, 51, 45, 33, 48,
                     44, 49, 39, 56, 34, 53, 46, 42, 50, 36, 29, 32]

const INITIAL = [58, 50, 42, 34, 26, 18, 10,  2, 60, 52, 44, 36, 28, 20, 12,  4,
                 62, 54, 46, 38, 30, 22, 14,  6, 64, 56, 48, 40, 32, 24, 16,  8,
                 57, 49, 41, 33, 25, 17,  9,  1, 59, 51, 43, 35, 27, 19, 11,  3,
                 61, 53, 45, 37, 29, 21, 13,  5, 63, 55, 47, 39, 31, 23, 15,  7]

const FINAL = [40,  8, 48, 16, 56, 24, 64, 32, 39,  7, 47, 15, 55, 23, 63, 31,
               38,  6, 46, 14, 54, 22, 62, 30, 37,  5, 45, 13, 53, 21, 61, 29,
               36,  4, 44, 12, 52, 20, 60, 28, 35,  3, 43, 11, 51, 19, 59, 27,
               34,  2, 42, 10, 50, 18, 58, 26, 33,  1, 41,  9, 49, 17, 57, 25]

const EXPANSION = [32,  1,  2,  3,  4,  5,  4,  5,  6,  7,  8,  9,  8,  9, 10, 11, 
                   12, 13, 12, 13, 14, 15, 16, 17, 16, 17, 18, 19, 20, 21, 20, 21, 
                   22, 23, 24, 25, 24, 25, 26, 27, 28, 29, 28, 29, 30, 31, 32,  1]

const PBOX = [16,  7, 20, 21, 29, 12, 28, 17,  1, 15, 23, 26,  5, 18, 31, 10, 
               2,  8, 24, 14, 32, 27,  3,  9, 19, 13, 30,  6, 22, 11,  4, 25]


function expand_key(r::Uint8, key::Uint64)
    k56 = permute_bits(key, 64, 56, KEY)
    c, d = split_28(k56)
    k = Array(Uint64, 0)
    for n in take(r, chain([1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1]))
        for _ in 1:n
            c, d = rotatel_28(c), rotatel_28(d)
        end
        k56 = join_28(c, d)
        push!(k, permute_bits(k56, 56, 48, COMPRESSION))
    end
    k
end


function f(r::Uint32, k::Uint32, sbox)
    r48::Uint64 = permute_bits(convert(Uint64, r), 32, 48, EXPANSION)
    
    permute_bits(r, PBOX)
end

function encrypt{S<:SBox}(s::State{S}, p::Uint64)
    p = permute_bits(p, INITIAL)
    l::Uint32, r::Uint32 = split_32(p)
    for i in 1:s.r
        if i > 1
            l, r = r, l
        end
        l = l $ f(r, s.k[i], i)
    end
    permute_bits(join_32(l, r), FINAL)
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


mask(n) = (one(Uint64) << n) - 1
const MASK_28 = mask(28)
const MASK_32 = mask(32)

split_28(k::Uint64) = (k >> 28 & MASK_28, k & MASK_28)
split_32(k::Uint64) = (convert(Uint32, k >> 32 & MASK_32), convert(Uint32, k & MASK_32))
 
join_28(c::Uint64, d::Uint64) = c << 28 | d
join_32(c::Uint32, d::Uint32) = convert(Uint64, c) << 32 | d

rotatel_28(n::Uint64) = MASK_28 & (n << 1 | n >>> 27)


function test_encrypt()
    z = State(0x0123456789abcdef, r=0x0)
    for r1 in take(10, rands(Uint64))
        @assert r1 == encrypt(z, r1)
    end
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
    test_encrypt()
end


tests()

end
