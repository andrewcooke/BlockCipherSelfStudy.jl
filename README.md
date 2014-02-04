# BlockCipherSelfStudy

## Introduction / Apology

Modern cryptography has moved on from block ciphers.  It's now all about
formal proofs of more complex systems.  So this is just me pootling around in
my free time, following [Bruce Schneier's self-study
course](https://github.com/andrewcooke/BlockCipherSelfStudy.jl/blob/master/doc/schneier-self-study.pdf).

## RC5 Without Rotation

[Defined
here](https://github.com/andrewcooke/BlockCipherSelfStudy.jl/blob/master/doc/rivest-rc5.pdf),
RC5 is a block cipher that uses addition, xor, and plaintext-dependent
rotations (although the amount of rotation cannot be determined from the
plaintext alone).

It is very configurable - the size of half-blocks, the number of rounds, and
the key size can all be varied.  Here, in addition, to reduce strength, we
disable rotations.

### State - 0 Rounds

Well,
[this](https://github.com/andrewcooke/BlockCipherSelfStudy.jl/blob/master/src/RC5.jl#L142)
is very easy.  A plaintext of 0 gives you the state.

### State - 1 Round

An adaptive, chosen plaintext
[attack](https://github.com/andrewcooke/BlockCipherSelfStudy.jl/blob/master/src/RC5.jl#L164)
that reverses the maths, step-by-step, to retrieve the internal state.
Getting the value of "the xor state" was tricky - I eventually realised that
comparing the results from encypting two values, differing only in one bit,
would (often) given the necessary information.

### Plaintext - Any Rounds, Lowest Bits

The lowest bits in each half-block can be
[tabulated](https://github.com/andrewcooke/BlockCipherSelfStudy.jl/blob/master/src/RC5.jl#L242)
independently of the rest of the bits (taking the two halves as a single
pair).  A single byte is very easy, giving rapid decryption of two bytes per
block.

### Plaintext - Any Rounds

Extending the above, an adaptive attack (requiring about two blocks per bit)
can
[search](https://github.com/andrewcooke/BlockCipherSelfStudy.jl/blob/master/src/RC5.jl#L295)
for the plaintext, bit by bit.  This works because the only mixing between
bits (without rotation) is via carry in additions.  So there are only 4
combinations of lowest bit (for the two half-blocks) that affect the lowest
bit.  Then four more for the next, and so on.

### State - 8 bits 2 Rounds / 32 bits 1 Round

A [GA
search](https://github.com/andrewcooke/BlockCipherSelfStudy.jl/blob/master/src/RC5.jl#L32)
that finds the state.  This weights scoring of successfully translated
half-blocks to build the state from the lsb and targets mutations at the least
significant incomplete bit.  So, for example, if all half-blocks have the
first 3 bits of a plaintext encrypted correctly, scoring and mutation target
the fourth bit, with some mutation at lower bits for carry.

### State - 32 bits 4 Rounds

A
[DFS](https://github.com/andrewcooke/BlockCipherSelfStudy.jl/blob/master/src/RC5.jl#L438)
that finds the state.  This searches from least to most significant bit.

Back-tracking for the first 2-4 bits dominates processing time.  Once those
bits are OK, typically, no further backtracking at that level is necessary and
more significant bits are found rapidly and (relatively) independently.  I do
not understand why - perhaps it is a bug, or perhaps it is simply that those
bits cascade more (so there is some kind of geometric of exponential
dependency on their values).  Adding a "beamwidth" limit to the search, or
inverting or reversing the bits tried, does not help.

### State - 32 bits 5 Rounds

As above, but using
[tabulated](https://github.com/andrewcooke/BlockCipherSelfStudy.jl/blob/master/src/RC5.jl#L561)
results.

Efficient pruning of the search is critical.  This is why so much time is
spent on the first few bits (see above) - because it is difficult to
discriminate good and bad answers at this level.  The approach here uses an
adaptive set of filters, updated every few seconds.

A solution for the 16-byte zero key, found after 1/4 of the state space is
explored, takes ~100 minutes.

### Linearity

RC5 without rotation is *not* linear.  In other words, whether `.` is addition
or xor,

```
p, q = encrypt(a.c, b.d)
r1, s1 = encrypt(a, b)
r2, s2 = encrypt(c, d)
p != r1.r2 && q != s1.s2
```

The source of the non-linearity is the combination of addition (with carry)
and xor.  If you describe a round as addition over words then the xor is
non-linear; if you describe it as addition over bits (ie xor) then the carry
operations are non-linear.

Yet various places assert that RC5 without rotation "is linear".

If linearity is taken to mean, loosely, that a solution can be composed from
smaller parts, then the only way that RC5 without rotation is linear, as far
as I can tell, is that the lowest bit is independent of other bits.  This
leads to attacks which progressively solve "upwards" from the least
significant bit, as described above.

The diagram below shows how carries ripple out when the least significant bit
of one half-block is changed (only half the encryption process is shown):

```
b a+s axb a+s axb a+s axb a+s a
    0       2       4       6  
                               
0 0+0 0x0 0+1 0x0 0+0 0x1 1+0 1
0 0 1 1 0 1 1 0 0 0 0 1 1 0 0 0
0 0 0 0 0 0 0 1 0 1 0 0 0 0 0 1
0 0 1 1 1 0 1 0 0 0 1 0 0 0 1 0
0 0 1 1 0 1 0 0 1 1 1 0 0 0 1 0
0 0 1 1 0 1 1 0 0 0 0 1 0 1 0 0
0 0 0 0 0 0 0 0 1 1 1 0 1 1 1 0
0 0 0 0 0 0 1 1 1 0 0 0 0 0 0 0

                              0
                        0 1    
                        1 1   0
                        1 1   1
                      1   1   1
                1 1   0 1      
              1 0              
  1   1   1   0 0       1 1   1
```

At the same time, my limited understanding of linear and differential attacks
suggests that RC5 wihout rotation is, in a sense, "too linear".  I can't find
a way to relate "distant" bits without also considering key expansion.  But
this may be my inexperience, or simply laziness (perhaps key expansion must be
included).

## RC5 With Rotation By Round

As above, but the first round rotation is 1 bit; the second round 2 bits; etc.

### Plaintext - 5 Rounds 

The influence of the first 4 bits on a randomly chosen key, with 5 rounds, is
shown below:

```
 0 444433211111000>^<8766667666665665
 1 5444332211100000>^<866666667766565
 2 55545543322210010>^<87666666667666
 3 665654433332111000>^<8666766667666
```

The output bit marked with `> <` is at `r(r+1)/2` - the cumulative shift
position - and most influenced (`^`; digits are 10% units relative to the
peak) by changing the input.

Clearly the influence of each bit is restricted to a a range of output bits at
and "above" the rotation.  So for each ciphertext character we can try using a
search over a limited number of bits.

In practice many character / key combinations can be found at 5 rounds, but
not at 6.

<!--
[![Build Status](https://travis-ci.org/andrewcooke/BlockCipherSelfStudy.jl.png)](https://travis-ci.org/andrewcooke/BlockCipherSelfStudy.jl)
-->
