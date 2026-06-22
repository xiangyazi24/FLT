# Q329-dm1: division-polynomial x-doubling certificate

## Executive answer

The missing closer is **not** `Adj/Inv` at shifted indices.  The correct local statement is a `Ψ₃`-saturated certificate.

For each parity of `m`, with the notation below,

```text
c3 * ΔDen = ADen * Adj + IDen * Inv + BDen * bRel
c3 * ΔNum = ANum * Adj + INum * Inv + BNum * bRel
```

where

```text
c3 = Ψ₃,
ΔDen = ΨSq(2m) - dupDenH(Φm, ΨSqm),
ΔNum = Φ(2m)   - dupNumH(Φm, ΨSqm),
bRel = b₂*b₆ - b₄^2 - 4*b₈.
```

So the finite relation list is exactly

```text
Adj(m), Inv(m), bRel,
```

plus universal-domain cancellation of `c3 = Ψ₃`.  There are **no shifted `Adj(m±1)` or `Inv(m±1)` instances** in the clean certificate, and no `preΨ(m±3)` variables are needed.

This also explains your CAS result: the unmultiplied `ΔDen` and `ΔNum` need not reduce to zero in the free local ring modulo `<Adj(m), Inv(m)>`.  The polynomial belongs to the saturation

```text
<Adj(m), Inv(m), bRel> : c3
```

not to the unsaturated ideal in free `P_{m-2},...,P_{m+2}` variables.

For Lean, prove the saturated identity over the universal domain, prove `Ψ₃ ≠ 0` there, cancel, and then transport the resulting unsaturated polynomial identity to arbitrary coefficient rings by the existing `map_ΨSq` / `map_Φ` lemmas.

---

## Current Mathlib status

I still do **not** find a Mathlib theorem that directly states division-polynomial x-coordinate composition/doubling, such as

```lean
W.ΨSq (2*m) = dupDenH W (W.Φ m) (W.ΨSq m)
W.Φ   (2*m) = dupNumH W (W.Φ m) (W.ΨSq m)
```

or the projective cross-product version.  The relevant available API is:

```lean
WeierstrassCurve.preΨ_even
WeierstrassCurve.preΨ_odd
WeierstrassCurve.ΨSq_even
WeierstrassCurve.ΨSq_odd
WeierstrassCurve.Φ
WeierstrassCurve.Φ_two
WeierstrassCurve.ΨSq_two
WeierstrassCurve.Affine.CoordinateRing.mk_ψ
WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq
WeierstrassCurve.Affine.CoordinateRing.mk_φ
WeierstrassCurve.map_preΨ
WeierstrassCurve.map_ΨSq
WeierstrassCurve.map_Φ
```

Mathlib also has the affine group-law lemma

```lean
WeierstrassCurve.Affine.addX_eq_addX_negY_sub
```

but there is not currently a ready bridge from that affine formula to `Φ n / ΨSq n` for division polynomials.

---

## 1. Local notation

Use the following local variables.

```text
x  := X
s  := Ψ₂Sq = 4*x^3 + b2*x^2 + 2*b4*x + b6
c3 := Ψ₃   = 3*x^4 + b2*x^3 + 3*b4*x^2 + 3*b6*x + b8
d4 := preΨ₄
   = 2*x^6 + b2*x^5 + 5*b4*x^4 + 10*b6*x^3 + 10*b8*x^2
     + (b2*b8 - b4*b6)*x + (b4*b8 - b6^2)

ell := 6*x^2 + b2*x + b4
eta := b6 + b4*x - 2*x^3

rho0 := 9*x^4 + 2*b2*x^3 + 4*b4*x^2 + 3*b6*x + b8
rho1 := 5*x^4 + b2*x^3 + 2*b4*x^2 + 2*b6*x + b8

Pm2 := preΨ(m-2)
Pm1 := preΨ(m-1)
P0  := preΨ(m)
P1  := preΨ(m+1)
P2  := preΨ(m+2)
```

The curve b-invariant relation is oriented as

```text
bRel := b2*b6 - b4^2 - 4*b8.
```

For parity, set

```text
m even: E2 = s^2, O2 = 1
m odd:  E2 = 1,   O2 = s^2
```

The local relations are

```text
Adj := Pm2*P2 - O2*Pm1*P1 + c3*P0^2.

Inv := c3*(P2*Pm1^2 + P1^2*Pm2 + E2*P0^3)
       - (d4 + s^2)*P1*P0*Pm1.
```

The local expansions are

```text
Z := ΨSq(m)
F := Φ(m)

m even: Z = P0^2*s,  F = x*Z - P1*Pm1
m odd:  Z = P0^2,    F = x*Z - P1*Pm1*s

L := Pm1^2*P2 - Pm2*P1^2
ΨSq(2m) = s*P0^2*L^2

Aplus  := P2*P0^3*E2 - Pm1*P1^3*O2
Aminus := P1*Pm1^3*O2 - Pm2*P0^3*E2
Φ(2m)  = x*s*P0^2*L^2 - Aplus*Aminus
```

The homogeneous doubling polynomials are

```text
dupDenH(F,Z) = 4*F^3*Z + b2*F^2*Z^2 + 2*b4*F*Z^3 + b6*Z^4

dupNumH(F,Z) = F^4 - b4*F^2*Z^2 - 2*b6*F*Z^3 - b8*Z^4
```

and the residuals are

```text
ΔDen := s*P0^2*L^2 - dupDenH(F,Z)
ΔNum := (x*s*P0^2*L^2 - Aplus*Aminus) - dupNumH(F,Z).
```

---

## 2. Denominator certificate, `m` even

For `m` even, use `E2=s^2`, `O2=1`, so

```text
Adj_even := Pm2*P2 - Pm1*P1 + c3*P0^2

Inv_even := c3*(P2*Pm1^2 + P1^2*Pm2 + s^2*P0^3)
            - (d4+s^2)*P1*P0*Pm1.
```

The exact certificate is

```text
c3 * ΔDen_even
= ADen_even * Adj_even + IDen_even * Inv_even + BDen_even * bRel
```

with

```text
ADen_even := -4*P0^2*P1^2*Pm1^2*s*c3

IDen_even := -P0^2*s*(P0^3*s^2 - P0*P1*Pm1*ell - P1^2*Pm2)
             + P0^2*Pm1^2*s*P2

BDen_even := P0^3*P1*Pm1*s
              *(P0^3*s^2*x^2
                - P0*P1*Pm1*rho0
                - P1^2*Pm2*x^2
                - P2*Pm1^2*x^2)
```

This is a direct `ring` identity after expanding the definitions of `s,c3,d4,ell,rho0`.

---

## 3. Numerator certificate, `m` even

For `m` even, the exact certificate is

```text
c3 * ΔNum_even
= ANum_even * Adj_even + INum_even * Inv_even + BNum_even * bRel
```

with

```text
ANum_even := P0^2*s*c3*(P0^4*s^3 - 4*P1^2*Pm1^2*x)

INum_even := -P0^2*s*(P0^3*s^2*x
                       + P0*P1*Pm1*eta
                       - P1^2*Pm2*x)
             + P0^2*Pm1^2*x*s*P2

BNum_even := P0^3*P1*Pm1*x*s
              *(P0^3*s^2*x^2
                - P0*P1*Pm1*rho1
                - P1^2*Pm2*x^2
                - P2*Pm1^2*x^2)
```

Again, this is a literal polynomial identity.

---

## 4. Denominator certificate, `m` odd

For `m` odd, use `E2=1`, `O2=s^2`, so

```text
Adj_odd := Pm2*P2 - s^2*Pm1*P1 + c3*P0^2

Inv_odd := c3*(P2*Pm1^2 + P1^2*Pm2 + P0^3)
           - (d4+s^2)*P1*P0*Pm1.
```

The exact certificate is

```text
c3 * ΔDen_odd
= ADen_odd * Adj_odd + IDen_odd * Inv_odd + BDen_odd * bRel
```

with

```text
ADen_odd := -4*P0^2*P1^2*Pm1^2*s*c3

IDen_odd := P0^2*s*(-P0^3 + P0*P1*Pm1*ell + P1^2*Pm2)
            + P0^2*Pm1^2*s*P2

BDen_odd := P0^3*P1*Pm1*s
             *(P0^3*x^2
               - P0*P1*Pm1*rho0
               - P1^2*Pm2*x^2
               - P2*Pm1^2*x^2)
```

---

## 5. Numerator certificate, `m` odd

The exact certificate is

```text
c3 * ΔNum_odd
= ANum_odd * Adj_odd + INum_odd * Inv_odd + BNum_odd * bRel
```

with

```text
ANum_odd := P0^2*c3*(P0^4 - 4*P1^2*Pm1^2*x*s)

INum_odd := P0^2*s*(-P0^3*x
                     - P0*P1*Pm1*eta
                     + P1^2*Pm2*x)
            + P0^2*Pm1^2*x*s*P2

BNum_odd := P0^3*P1*Pm1*x*s
             *(P0^3*x^2
               - P0*P1*Pm1*rho1
               - P1^2*Pm2*x^2
               - P2*Pm1^2*x^2)
```

---

## 6. One-file CAS check

This is the exact Sympy check I used for the four certificates above.  It uses the same orientations as the displayed formulas.

```python
import sympy as sp

x,b2,b4,b6,b8 = sp.symbols('x b2 b4 b6 b8')
Pm2,Pm1,P0,P1,P2 = sp.symbols('Pm2 Pm1 P0 P1 P2')

s  = 4*x**3 + b2*x**2 + 2*b4*x + b6
c3 = 3*x**4 + b2*x**3 + 3*b4*x**2 + 3*b6*x + b8
d4 = (2*x**6 + b2*x**5 + 5*b4*x**4 + 10*b6*x**3 + 10*b8*x**2
      + (b2*b8 - b4*b6)*x + (b4*b8 - b6**2))
ell  = 6*x**2 + b2*x + b4
eta  = b6 + b4*x - 2*x**3
rho0 = 9*x**4 + 2*b2*x**3 + 4*b4*x**2 + 3*b6*x + b8
rho1 = 5*x**4 + b2*x**3 + 2*b4*x**2 + 2*b6*x + b8
bRel = b2*b6 - b4**2 - 4*b8

for parity in ['even','odd']:
    E2 = s**2 if parity == 'even' else 1
    O2 = 1    if parity == 'even' else s**2
    E  = s    if parity == 'even' else 1
    O  = 1    if parity == 'even' else s

    Z = P0**2 * E
    F = x*Z - P1*Pm1*O
    L = Pm1**2*P2 - Pm2*P1**2

    Psi2 = s*P0**2*L**2
    dupDen = 4*F**3*Z + b2*F**2*Z**2 + 2*b4*F*Z**3 + b6*Z**4
    dupNum = F**4 - b4*F**2*Z**2 - 2*b6*F*Z**3 - b8*Z**4

    Aplus  = P2*P0**3*E2 - Pm1*P1**3*O2
    Aminus = P1*Pm1**3*O2 - Pm2*P0**3*E2
    Phi2   = x*Psi2 - Aplus*Aminus

    Adj = Pm2*P2 - O2*Pm1*P1 + c3*P0**2
    Inv = c3*(P2*Pm1**2 + P1**2*Pm2 + E2*P0**3) - (d4+s**2)*P1*P0*Pm1

    if parity == 'even':
        ADen = -4*P0**2*P1**2*Pm1**2*s*c3
        IDen = -P0**2*s*(P0**3*s**2 - P0*P1*Pm1*ell - P1**2*Pm2) + P0**2*Pm1**2*s*P2
        BDen = P0**3*P1*Pm1*s*(P0**3*s**2*x**2 - P0*P1*Pm1*rho0 - P1**2*Pm2*x**2 - P2*Pm1**2*x**2)

        ANum = P0**2*s*c3*(P0**4*s**3 - 4*P1**2*Pm1**2*x)
        INum = -P0**2*s*(P0**3*s**2*x + P0*P1*Pm1*eta - P1**2*Pm2*x) + P0**2*Pm1**2*x*s*P2
        BNum = P0**3*P1*Pm1*x*s*(P0**3*s**2*x**2 - P0*P1*Pm1*rho1 - P1**2*Pm2*x**2 - P2*Pm1**2*x**2)
    else:
        ADen = -4*P0**2*P1**2*Pm1**2*s*c3
        IDen = P0**2*s*(-P0**3 + P0*P1*Pm1*ell + P1**2*Pm2) + P0**2*Pm1**2*s*P2
        BDen = P0**3*P1*Pm1*s*(P0**3*x**2 - P0*P1*Pm1*rho0 - P1**2*Pm2*x**2 - P2*Pm1**2*x**2)

        ANum = P0**2*c3*(P0**4 - 4*P1**2*Pm1**2*x*s)
        INum = P0**2*s*(-P0**3*x - P0*P1*Pm1*eta + P1**2*Pm2*x) + P0**2*Pm1**2*x*s*P2
        BNum = P0**3*P1*Pm1*x*s*(P0**3*x**2 - P0*P1*Pm1*rho1 - P1**2*Pm2*x**2 - P2*Pm1**2*x**2)

    assert sp.expand(c3*(Psi2 - dupDen) - (ADen*Adj + IDen*Inv + BDen*bRel)) == 0
    assert sp.expand(c3*(Phi2 - dupNum) - (ANum*Adj + INum*Inv + BNum*bRel)) == 0

print('all certificates verified')
```

---

## 7. Lean encoding shape

Use a parity split.  The local polynomial lemmas should be stated as saturated identities first.

```lean
lemma Ψ₃_mul_ΨSq_two_mul_sub_dupDen_even
    (hm : Even m) :
    W.Ψ₃ *
      (W.ΨSq (2*m) - dupDenH W (W.Φ m) (W.ΨSq m)) = 0 := by
  -- rewrite by:
  --   W.ΨSq_even m
  --   W.preΨ_odd m
  --   W.preΨ_odd (m-1)
  --   W.Φ
  --   parity facts from hm
  -- then use linear_combination with:
  --   ADen_even * Adj_even
  --   IDen_even * Inv_even
  --   BDen_even * bRel
  -- and close by ring_nf.
  sorry

lemma Ψ₃_mul_Φ_two_mul_sub_dupNum_even
    (hm : Even m) :
    W.Ψ₃ *
      (W.Φ (2*m) - dupNumH W (W.Φ m) (W.ΨSq m)) = 0 := by
  -- same expansion, with ANum_even / INum_even / BNum_even
  sorry

lemma Ψ₃_mul_ΨSq_two_mul_sub_dupDen_odd
    (hm : ¬ Even m) :
    W.Ψ₃ *
      (W.ΨSq (2*m) - dupDenH W (W.Φ m) (W.ΨSq m)) = 0 := by
  -- same expansion, with ADen_odd / IDen_odd / BDen_odd
  sorry

lemma Ψ₃_mul_Φ_two_mul_sub_dupNum_odd
    (hm : ¬ Even m) :
    W.Ψ₃ *
      (W.Φ (2*m) - dupNumH W (W.Φ m) (W.ΨSq m)) = 0 := by
  -- same expansion, with ANum_odd / INum_odd / BNum_odd
  sorry
```

The relation `Adj` comes from the already-proved adjacent Somos/AddRel for the `preΨ` EDS.  The relation `Inv` is the invariant relation for that same `preΨ` EDS with parameters

```text
b^2 := s^2,
c   := c3,
d   := d4.
```

For `bRel`, either use a lemma

```lean
lemma b_relation (W : WeierstrassCurve R) :
    W.b₂ * W.b₆ - W.b₄^2 - 4 * W.b₈ = 0 := by
  rw [WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring
```

or simply unfold `b₂ b₄ b₆ b₈` and let `ring_nf` discharge it.

Then cancel only in the universal domain:

```lean
lemma Ψ₃_ne_zero_universal : Wuniv.Ψ₃ ≠ 0 := by
  -- Either unfold Ψ₃ and inspect the X^4 coefficient, or use degree/leading coefficient lemmas.
  -- Over the universal integral domain, the leading coefficient is 3, hence nonzero.
  sorry

lemma ΨSq_two_mul_universal (m : ℤ) :
    Wuniv.ΨSq (2*m) = dupDenH Wuniv (Wuniv.Φ m) (Wuniv.ΨSq m) := by
  have hsat : Wuniv.Ψ₃ *
      (Wuniv.ΨSq (2*m) - dupDenH Wuniv (Wuniv.Φ m) (Wuniv.ΨSq m)) = 0 := by
    by_cases hm : Even m
    · exact Ψ₃_mul_ΨSq_two_mul_sub_dupDen_even (W := Wuniv) hm
    · exact Ψ₃_mul_ΨSq_two_mul_sub_dupDen_odd (W := Wuniv) hm
  have hsub : Wuniv.ΨSq (2*m) - dupDenH Wuniv (Wuniv.Φ m) (Wuniv.ΨSq m) = 0 :=
    mul_left_cancel₀ Ψ₃_ne_zero_universal hsat
  exact sub_eq_zero.mp hsub

lemma Φ_two_mul_universal (m : ℤ) :
    Wuniv.Φ (2*m) = dupNumH Wuniv (Wuniv.Φ m) (Wuniv.ΨSq m) := by
  have hsat : Wuniv.Ψ₃ *
      (Wuniv.Φ (2*m) - dupNumH Wuniv (Wuniv.Φ m) (Wuniv.ΨSq m)) = 0 := by
    by_cases hm : Even m
    · exact Ψ₃_mul_Φ_two_mul_sub_dupNum_even (W := Wuniv) hm
    · exact Ψ₃_mul_Φ_two_mul_sub_dupNum_odd (W := Wuniv) hm
  have hsub : Wuniv.Φ (2*m) - dupNumH Wuniv (Wuniv.Φ m) (Wuniv.ΨSq m) = 0 :=
    mul_left_cancel₀ Ψ₃_ne_zero_universal hsat
  exact sub_eq_zero.mp hsub
```

Finally transport by the existing map lemmas:

```lean
WeierstrassCurve.map_Ψ₂Sq
WeierstrassCurve.map_Ψ₃
WeierstrassCurve.map_preΨ₄
WeierstrassCurve.map_preΨ
WeierstrassCurve.map_ΨSq
WeierstrassCurve.map_Φ
```

The arbitrary-ring/field theorem should be obtained by mapping from the universal theorem; do not cancel `Ψ₃` in the target ring.

---

## 8. Coordinate-ring route

The coordinate-ring route is useful for sanity checks but is not currently shorter in Mathlib.

Available lemmas:

```lean
WeierstrassCurve.Affine.CoordinateRing.mk_ψ
WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq
WeierstrassCurve.Affine.CoordinateRing.mk_φ
```

These let you rewrite in `R[W]` as

```text
mk(W.ψ n)^2 = mk(C (W.ΨSq n))
mk(W.φ n)   = mk(C (W.Φ n))
```

and your unconditional Ward theorem applies directly to the bivariate sequence

```lean
W.ψ n = normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n.
```

A denominator proof in the coordinate ring would have the conceptual form

```text
mk(C (dupDenH(Φm,ΨSqm)))
= mk(W.ψ (2*m)^2)
= mk(C (W.ΨSq (2*m))).
```

The numerator proof would similarly target

```text
mk(C (dupNumH(Φm,ΨSqm)))
= mk(W.φ (2*m))
= mk(C (W.Φ (2*m))).
```

However, to make the middle equalities rigorous from affine duplication, Mathlib would need either:

```text
ω_n / y-coordinate division-polynomial API,
```

or a homogeneous Kummer-line duplication theorem already stated in the coordinate ring.  The Basic file still marks `ωₙ` as TODO, and the available affine formula `Affine.addX_eq_addX_negY_sub` is not connected to the division-polynomial `Φ/ΨSq` API.

So the coordinate-ring path does avoid some `preΨ` parity bookkeeping only after building new infrastructure.  For the current repo, the saturated local certificate above is the most direct path.

---

## 9. Final projective equality

After the exact identities are proved and transported,

```lean
lemma divisionPolynomial_x_doubling_projective (m : ℤ) :
    W.Φ (2*m) * dupDenH W (W.Φ m) (W.ΨSq m)
      = W.ΨSq (2*m) * dupNumH W (W.Φ m) (W.ΨSq m) := by
  rw [ΨSq_two_mul, Φ_two_mul]
  ring
```

The projective scalar is `1`; the `Ψ₃` only appears internally as the saturation/cancellation device for proving the exact identities.
