# Verification of Remco's full 256x256 bit multiplication

This repo attempts to verify Remco's widely used `mulDiv` function.

At the moment it **only verifies** that the computation of the upper 256 bits of the 512 bit product
via `sub(sub(x1, x0), lt(x1, x0))` is verified.

Furthermore it verifies a specialization of `fullMulDiv` where the denominator is fixed to `2^128`.


Credit to Remco Bloemen under MIT license: 2π.com/17/chinese-remainder-theorem/
