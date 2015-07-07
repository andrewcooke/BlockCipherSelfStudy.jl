
module DES

using ..Assert: @assert3f
using ..Solve: rands
using ..Tasks: take
using ..Blocks: chain

export tests


# An implementation of DES.  Encryption only, and not very efficient.


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


mask(n) = (one(Uint64) << n) - 1
const MASK_28 = mask(28)
const MASK_32 = mask(32)
const MASK_6 = mask(6)
const MASK_4 = mask(4)
const MASK_2 = mask(2)


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

const PBOX = [16,  7, 20, 21, 29, 12, 28, 17,  1, 15, 23, 26,  5, 18, 31, 10, 
               2,  8, 24, 14, 32, 27,  3,  9, 19, 13, 30,  6, 22, 11,  4, 25]

const SBOX = Array(Uint32, 16, 4, 8)
SBOX[:,:,1] = [14  4 13  1  2 15 11  8  3 10  6 12  5  9  0  7;
                0 15  7  4 14  2 13  1 10  6 12 11  9  5  3  8;
                4  1 14  8 13  6  2 11 15 12  9  7  3 10  5  0;
               15 12  8  2  4  9  1  7  5 11  3 14 10  0  6 13]'
SBOX[:,:,2] = [15  1  8 14  6 11  3  4  9  7  2 13 12  0  5 10;
                3 13  4  7 15  2  8 14 12  0  1 10  6  9 11  5;
                0 14  7 11 10  4 13  1  5  8 12  6  9  3  2 15;
               13  8 10  1  3 15  4  2 11  6  7 12  0  5 14  9]'
SBOX[:,:,3] = [10  0  9 14  6  3 15  5  1 13 12  7 11  4  2  8;
               13  7  0  9  3  4  6 10  2  8  5 14 12 11 15  1;
               13  6  4  9  8 15  3  0 11  1  2 12  5 10 14  7;
                1 10 13  0  6  9  8  7  4 15 14  3 11  5  2 12]'
SBOX[:,:,4] = [ 7 13 14  3  0  6  9 10  1  2  8  5 11 12  4 15;
               13  8 11  5  6 15  0  3  4  7  2 12  1 10 14  9;
               10  6  9  0 12 11  7 13 15  1  3 14  5  2  8  4;
                3 15  0  6 10  1 13  8  9  4  5 11 12  7  2 14]'
SBOX[:,:,5] = [ 2 12  4  1  7 10 11  6  8  5  3 15 13  0 14  9;
               14 11  2 12  4  7 13  1  5  0 15 10  3  9  8  6;
                4  2  1 11 10 13  7  8 15  9 12  5  6  3  0 14;
               11  8 12  7  1 14  2 13  6 15  0  9 10  4  5  3]'
SBOX[:,:,6] = [12  1 10 15  9  2  6  8  0 13  3  4 14  7  5 11;
               10 15  4  2  7 12  9  5  6  1 13 14  0 11  3  8;
                9 14 15  5  2  8 12  3  7  0  4 10  1 13 11  6;
                4  3  2 12  9  5 15 10 11 14  1  7  6  0  8 13]'
SBOX[:,:,7] = [ 4 11  2 14 15  0  8 13  3 12  9  7  5 10  6  1;
               13  0 11  7  4  9  1 10 14  3  5 12  2 15  8  6;
                1  4 11 13 12  3  7 14 10 15  6  8  0  5  9  2;
                6 11 13  8  1  4 10  7  9  5  0 15 14  2  3 12]'
SBOX[:,:,8] = [13  2  8  4  6 15 11  1 10  9  3 14  5  0 12  7;
                1 15 13  8 10  3  7  4 12  5  6 11  0 14  9  2;
                7 11  4  1  9 12 14  2  0  6 10 13 15  3  5  8;
                2  1 14  7  4 10  8 13 15 12  9  0  3  5  6 11]'


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


split_28(k::Uint64) = (k >> 28 & MASK_28, k & MASK_28)
split_32(k::Uint64) = (convert(Uint32, k >> 32 & MASK_32), convert(Uint32, k & MASK_32))
 
join_28(c::Uint64, d::Uint64) = c << 28 | d
join_32(c::Uint32, d::Uint32) = convert(Uint64, c) << 32 | d

rotatel_28(n::Uint64) = MASK_28 & (n << 1 | n >>> 27)


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


circlify(n, val) = val << 1 | val >>> (n-1) | val << (n+1)

function f(r::Uint32, k48::Uint64, ::Type{WithSBox})
    out::Uint32 = zero(Uint32)
    w::Uint64 = convert(Uint64, r)
    # the "expansion permutation" is equivalent to using a sliding window
    # along a circularly repeating value, shifting 4 digits each time
    w = circlify(32, w) << 14
    for i in 1:8
        # process the top-most 6 bits
        in = MASK_6 & ((w $ k48) >> 42)
        row = ((in >> 4) & 0x2) | (in & 0x1)
        col = MASK_4 & (in >>> 1)
        out = (out << 4) | SBOX[col+1,row+1,i]
        w, k48 = w << 4, k48 << 6
    end
    permute_bits(out, PBOX)
end

function f(r::Uint32, k48::Uint64, ::Type{WithoutSBox})
    out::Uint32 = zero(Uint32)
    w::Uint64 = convert(Uint64, r) << 15
    for i in 1:8
        # checked by hand against the sbox equivalent
        out = (out << 4) | convert(Uint32, MASK_4 & ((w $ k48) >> 43))
        w, k48 = w << 4, k48 << 6
    end
    permute_bits(out, PBOX)
end

function encrypt{S<:SBox}(s::State{S}, p::Uint64)
    p = permute_bits(p, INITIAL)
    l::Uint32, r::Uint32 = split_32(p)
    for i in 1:s.r
        if i > 1
            l, r = r, l
        end
        l = l $ f(r, s.k[i], s.sbox)
    end
    permute_bits(join_32(l, r), FINAL)
end


# --- tests

function test_encrypt()
    z = State(0x0123456789abcdef, r=0x0)
    for r1 in take(10, rands(Uint64))
        @assert r1 == encrypt(z, r1)
    end
    # http://cryptomanager.com/tv.html
    s = State(0x752878397493CB70)
    @assert3f hex encrypt(s, 0x1122334455667788) == 0xB5219EE81AA7499D
    @assert3f hex encrypt(s, 0x99aabbccddeeff00) == 0x2196687E13973856
    println("test_encrypt ok")
end

function test_permutation()
    for r1 in take(10, rands(Uint8))
        r2 = permute_bits(r1, [1,2,3,4,5,6,7,8])
        @assert r1 == r2
    end
    r1 = permute_bits(0b11000000, [2,3,4,5,6,7,8,1])
    @assert r1 == 0b10000001
    println("test_permutation ok")
end

function test_schedule()
    # http://www.herongyang.com/Cryptography/DES-Illustration-DES-Key-Schedule-Output.html
    s = State(0b0001001100110100010101110111100110011011101111001101111111110001)
    @assert s.k[1] == 0b000110110000001011101111111111000111000001110010
    @assert s.k[16] == 0b110010110011110110001011000011100001011111110101
    println("test_schedule ok")
end

function tests()
    test_permutation()
    test_schedule()
    test_encrypt()
    println("DES.tests ok")
end

end
