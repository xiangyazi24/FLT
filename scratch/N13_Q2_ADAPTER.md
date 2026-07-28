# N13 first-jet `Q_2` adapter audit

Audit date: 2026-07-27.

## What is now formal

`FLT/Assumptions/MazurProof/N13LocalDlogRegimes.lean` contains a
non-enumerative implementation of both valuation regimes.

The finite quotient is the concrete ring

```text
DualNumber F8 = F8[epsilon]/epsilon^2,
F8 = F2[alpha]/(alpha^3+alpha+1).
```

The file proves:

```text
i     |-> 1+epsilon,
theta |-> alpha
```

satisfies both `i^2=-1` and the exact Gaussian cubic relation.  Thus the
two dual numbers are compatible with the structural local presentation.

For `xbar : F2`, the element

```text
xbar-alpha
```

is proved nonzero structurally (`alpha` is neither `0` nor `1`), packaged
as a dual-number unit, and its ramified logarithm is proved zero.

For `x : Q_2` with nonnegative valuation, Mathlib's equivalence

```text
Padic.norm_le_one_iff_val_nonneg
```

packages `x` as an element of `Z_2`.  The actual ring homomorphism

```text
Z_2 -> ZMod 2 -> F8 -> DualNumber F8
```

is `padicScalarDualHom`; the integral raw jet is proved to be the image of
`x` minus `thetaDual`.

For `x : Q_2` with negative valuation, the file proves:

```text
x != 0,
0 < valuation (x^-1),
toZMod (x^-1) = 0.
```

The last step uses `PadicInt.mem_span_pow_iff_le_valuation`,
`PadicInt.maximalIdeal_eq_span_p`, and `PadicInt.ker_toZMod`, not a
postulated residue property.  The normalized jet

```text
1 - reduction(x^-1)*thetaDual
```

is therefore exactly `1`, and its ramified logarithm is zero.  The generic
field identity

```text
x-theta = x * (1-x^-1*theta)
```

is also formalized; this is the rational scalar removed by fake descent.

## Existing completion infrastructure

The repository and Mathlib already provide most abstract completion
machinery:

```text
Padic.addValuation
Padic.norm_le_one_iff_val_nonneg
PadicInt.toZMod
PadicInt.ker_toZMod
PadicInt.mem_span_pow_iff_le_valuation

HeightOneSpectrum.adicCompletion
HeightOneSpectrum.adicCompletionIntegers
HeightOneSpectrum.ResidueFieldEquivCompletionResidueField
HeightOneSpectrum.Extension.adicCompletionIntegersRingHom
HeightOneSpectrum.adicCompletion.mem_completionIdeal_pow
```

In particular, `FLT/DedekindDomain/Completion/BaseChange.lean` supplies
maps between completions at a prime and a chosen prime above it, with the
valuation formula for that map.  The missing piece is not a general
notion of completion or residue field.

## Shortest remaining semantic gap

To turn the finite character into a homomorphism on the actual local
sextic algebra, one fixed-instance theorem is still required:

```text
O_L,P / P^2  ~=  DualNumber F8
```

with the equivalence sending

```text
1-i   |-> epsilon,
i     |-> 1+epsilon,
theta |-> alpha.
```

More explicitly, the shortest completion route has four steps.

1. Equip the irreducible sextic algebra with its number-field structure
   and select the height-one prime `P` above `2`.

2. Prove the fixed factorization data

   ```text
   (2)=P^2,  residueDegree(P/2)=3,
   ```

   preferably from the Gaussian cubic presentation.  The residue cubic
   `T^3+T+1` is already proved irreducible in
   `N13LocalDlogTwo.lean`.

3. Construct the second-order quotient equivalence above.  The repository
   has a residue-field equivalence modulo `P`, but no ready-made theorem
   identifying a ramified length-two quotient modulo `P^2` with a
   trivial square-zero extension.  This is the genuinely missing adapter.

4. Prove compatibility of the local embedding with the three displayed
   generators.  Once this is done, the two regime theorems in
   `N13LocalDlogRegimes.lean` immediately show that every affine local
   Kummer value lies in the kernel of the first jet.

An alternative is to define the Gaussian `Z_2` order directly and prove
its quotient by `(1-i)^2` is the dual-number ring.  This avoids the general
completion API, but one must still prove that this order is the relevant
local integer ring (or at least that every Kummer value used is a unit in
it).  Consequently it does not remove the fixed local-order theorem; it
only repackages it.

No strong Hensel square theorem and no `P^5` ray-class computation is
needed for the two coordinate-jet vanishings proved here.

In particular, the current production theorem is **not yet** a theorem
about the actual Mumford/Jacobian Kummer map.  It proves `dlog=0` for the
two coordinate jets after `Q_2` reduction.  Applying it to a Jacobian
class still requires the local-order quotient equivalence and a theorem
identifying the relevant Mumford/Kummer value with the corresponding
coordinate jet.
