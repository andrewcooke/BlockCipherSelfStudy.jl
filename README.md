# BlockCipherSelfStudy

## Introduction / Apology

Modern cryptography has moved on from block ciphers.  It's now all about
formal proofs of more complex systems.  So this is just me pootling around in
my free time, following [Bruce Schneier's self-study
course](https://github.com/andrewcooke/BlockCipherSelfStudy.jl/blob/master/doc/schneier-self-study.pdf).

## RC5

[Defined
here](https://github.com/andrewcooke/BlockCipherSelfStudy.jl/blob/master/doc/rivest-rc5.pdf),
RC5 is a block cipher that uses addition, xor, and plaintext-dependent
rotations (although the amount of rotation cannot be determined from the
plaintext alone).

It is very configurable - the size of half-blocks, the number of rounds, and
the key size can all be varied.  Here, in addition, to reduce strength, we
modify how / when rotations are applied.

### State - 0 Rounds, No Rotation

Well,
[this](https://github.com/andrewcooke/BlockCipherSelfStudy.jl/blob/master/src/RC5.jl#L142)
is very easy.  A plaintext of 0 gives you the state.

### State - 1 Round, No Rotation

An adaptive, chosen plaintext
[attack](https://github.com/andrewcooke/BlockCipherSelfStudy.jl/blob/master/src/RC5.jl#L164)
that reverses the maths, step-by-step, to retrieve the internal state.
Getting the value of "the xor state" was tricky - I eventually realised that
comparing the results from encypting two values, differing only in one bit,
would (often) given the necessary information.

### Plaintext - Any Rounds, No Rotation, Lowest Bits

The lowest bits in each half-block can be
[tabulated](https://github.com/andrewcooke/BlockCipherSelfStudy.jl/blob/master/src/RC5.jl#L242)
independently of the rest of the bits (taking the two halves as a single
pair).  A single byte is very easy, giving rapid decryption of two bytes per
block.

### Plaintext - Any Rounds, No Rotation

Extending the above, an adaptive attack (requiring about two blocks per bit)
can
[search](https://github.com/andrewcooke/BlockCipherSelfStudy.jl/blob/master/src/RC5.jl#L295)
for the plaintext, bit by bit.  This works because the only mixing between
bits (without rotation) is via carry in additions.  So there are only 4
combinations of lowest bit (for the two half-blocks) that affect the lowest
bit.  Then four more for the next, and so on.

### State - 8 bits 2 Rounds / 32 bits 1 Round, No Rotation

A [GA
search](https://github.com/andrewcooke/BlockCipherSelfStudy.jl/blob/master/src/RC5.jl#L32)
that finds the state.  This weights scoring of successfully translated
half-blocks to build the state from the lsb and targets mutations at the least
significant incomplete bit.  So, for example, if all half-blocks have the
first 3 bits of a plaintext encrypted correctly, scoring and mutation target
the fourth bit, with some mutation at lower bits for carry.

### State - 32 bits 4 Rounds, No Rotation

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

### State - 32 bits 5 Rounds, No Rotation

As above, but using
[tabulated](https://github.com/andrewcooke/BlockCipherSelfStudy.jl/blob/master/src/RC5.jl#L561)
results.

Efficient pruning of the search is critical.  This is why so much time is
spent on the first few bits (see above) - because it is difficult to
discriminate good and bad answers at this level.  The approach here uses an
adaptive set of filters, updated every few seconds.

A solution for the 16-byte zero key, found after 1/4 of the state space is
explored, takes ~100 minutes.

### Ripple Diagrams

Trying to understand linear cryptanalysis (and/or just simple linear
functions), I generated plots that show how carries ripple through the
encryption process.

The diagram below is for 8-bit half-blocks, three rounds.  It shows the
encryption for a,b = 0,0 and then the changes to that when the lowest bit of
a, and the next highest bit of b, are changed.

```
a s a b s b a b a s a b a b s b a b a s a b a b s b a b a s a b a b s b a
  0     1         2         3         4         5         6         7    
                                                                         
0+0=0 0+0=0 0x0=0+1=0 0x0=0+1=0 0x0=0+0=0 0x0=0+0=1 0x1=1+0=1 1x1=0+1=0 1
0 1 1 0 0 0 1 0 1 1 0 0 0 0 1 0 0 0 0 0 1 0 1 1 1 1 1 1 0 0 0 1 0 1 0 0 0
0 0 0 0 0 0 0 0 0 0 1 0 1 1 0 0 1 0 1 0 0 0 0 0 1 0 0 0 0 0 1 0 1 1 1 0 1
0 1 1 0 1 1 1 1 0 1 0 1 0 1 1 0 0 0 0 1 0 0 0 0 1 0 0 0 0 1 0 0 0 0 0 0 0
0 1 1 0 0 0 1 0 1 0 0 0 0 0 1 1 0 1 1 1 0 1 0 1 0 0 0 0 0 1 0 0 0 0 0 0 0
0 1 1 0 0 0 1 0 1 1 0 0 0 0 0 0 0 0 0 0 1 0 1 1 0 0 1 0 1 0 0 0 0 0 1 1 0
0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1 0 1 1 1 0 1 0 1 1 1 0 1 1 1 0 1 0 1 0 1 0
0 0 0 0 0 0 0 0 0 1 1 0 1 1 0 1 1 1 0 0 0 1 0 1 1 0 0 0 0 0 0 0 0 0 0 0 0

                                                            0   0 1     0
                                                  0   0 1     0   0   1  
                                                  1   1 1   0 1 0       0
                                                  1   1 1   1 1 1     1 1
                                        1   1 0     1   1   1   1 1     1
                              1   1 1   0 1 0     1 0 1       1   1   0  
                    1   1 1   0 1 0       0   0                          
1   1       1   1   0   0 0   0 0 0       0   0   1   1 1   1 1 1       1
                                                                         

                              1   1 1     1   1   1   1 1   1 1 1       1
                              0   0 0   1 0 1       1   1   1   1 1   1 1
                    1   1 1     1   1                                    
      1   1   1 1     1   1   0   0 0   1 0 1     0 1 0       0   0   0  
1   1       1   1   0   0 0   0 0 0       0   0   1   1 1   1 1 1       1
```

<!--
[![Build Status](https://travis-ci.org/andrewcooke/BlockCipherSelfStudy.jl.png)](https://travis-ci.org/andrewcooke/BlockCipherSelfStudy.jl)
-->
