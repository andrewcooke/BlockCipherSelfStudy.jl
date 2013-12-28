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

Something of an intermediate step between the attacks above and below.  The
lowest bits in each half-block can be
[tabulated](https://github.com/andrewcooke/BlockCipherSelfStudy.jl/blob/master/src/RC5.jl#L242)
independently of the rest of the bits (taking the two halves as a single
pair).  A single byte is very easy, giving rapid decryption of two bytes per
block.

### Plaintext - Any Rounds, No Rotation

Extending the above, an adaptive attack (requiring about two blocks per bit)
can
[search](https://github.com/andrewcooke/BlockCipherSelfStudy.jl/blob/master/src/RC5.jl#L300)
for the plaintext, bit by bit.  This works because the only mixing between
bits (without rotation) is via carry in additions.  So there are only 4
combinations of lowest bit (for the two half-blocks) that affect the lowest
bit.  Then four more for the next, and so on.

<!--
[![Build Status](https://travis-ci.org/andrewcooke/BlockCipherSelfStudy.jl.png)](https://travis-ci.org/andrewcooke/BlockCipherSelfStudy.jl)
-->
