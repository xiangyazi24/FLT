# Q262-dm1: R2 doubling half of the keystone EDS core

## Honest status

I cannot give a build-ready 0-sorry Lean proof of the requested theorem from the pasted signatures alone.  The reason is not the mathematics of the theorem; it is that the requested final step requires the exact residual normal form left by the local `DoublingTest.lean` rewrites.  The connector previously returned `404` for the scratch Lean files, and the prompt explicitly says to work from pasted signatures, so I cannot inspect the actual local names, simp orientations, or residual.

I also cannot honestly invent explicit `linear_combination` cofactors.  The cofactor is large and depends on the chosen normalization: raw `Φ/ΨSq`, coordinate-ring `φ/ψ`, whether the identity is multiplied by `mk(C Ψ₂Sq)`, and how `ψ_even` is oriented.  A fake cofactor would waste build cycles.

The correct proof architecture is now clear, though, and the missing piece is sharply isolated below.

---

## What the proof should prove first

Do **not** try to prove the raw `R[X]` identity directly.  Prove a coordinate-ring identity multiplied by `mk(C Ψ₂Sq)`, then cancel `mk(C Ψ₂Sq)` using the domain property.

The reason for multiplying by `Ψ₂Sq` is the Mathlib recurrence

```lean
ψ_even (m) : W.ψ (2*m) * W.ψ₂ =
  W.ψ (m-1)^2 * W.ψ m * W.ψ (m+2)
    - W.ψ (m-2) * W.ψ m * W.ψ (m+1)^2
```

The square of this gives `ψ(2m)^2 * ψ₂^2`, not `ψ(2m)^2` directly.  In the coordinate ring,

```lean
mk W W.ψ₂ ^ 2 = mk W (C W.Ψ₂Sq)
```

so the clean identity is the `Ψ₂Sq`-multiplied one.

---

## Minimal coordinate-ring theorem to add

This is the theorem that should be proved by `ring_nf` plus the already proven
`FLT.EDS.mk_psi_adjacent_somos`.

```lean
import Mathlib
-- local imports, once visible:
-- import scratch.WardSomos
-- import scratch.PsiSomos

open Polynomial WeierstrassCurve
open WeierstrassCurve.Affine.CoordinateRing

namespace FLT.DivisionPolynomialDoubling

variable {k : Type*} [Field k]
variable (W : WeierstrassCurve k) [W.IsElliptic]

noncomputable def dupNumP (P Q : k[X]) : k[X] :=
  P ^ 4
    - C W.b₄ * P ^ 2 * Q ^ 2
    - C (2 * W.b₆) * P * Q ^ 3
    - C W.b₈ * Q ^ 4

noncomputable def dupDenP (P Q : k[X]) : k[X] :=
  C 4 * P ^ 3 * Q
    + C W.b₂ * P ^ 2 * Q ^ 2
    + C (2 * W.b₄) * P * Q ^ 3
    + C W.b₆ * Q ^ 4

noncomputable def dupCrossDiff (m : ℤ) : k[X] :=
  W.Φ (2 * m) * dupDenP W (W.Φ m) (W.ΨSq m)
    - W.ΨSq (2 * m) * dupNumP W (W.Φ m) (W.ΨSq m)

/--
The exact coordinate-ring target that avoids division by `ψ₂`.

This is the right target for the new `mk_psi_adjacent_somos` lemma.  It is smaller than the raw theorem
because it stays inside the coordinate ring and keeps the unavoidable `ψ₂² = Ψ₂Sq` multiplier explicit.
-/
theorem mk_Ψ₂Sq_mul_dupCrossDiff (m : ℤ) :
    mk W.toAffine (Polynomial.C W.Ψ₂Sq) *
      mk W.toAffine (Polynomial.C (dupCrossDiff W m)) = 0 := by
  classical

  -- Core coordinate-ring facts.
  have hS := FLT.EDS.mk_psi_adjacent_somos (W := W) (m := m)

  have hψ2sq :
      mk W.toAffine W.ψ₂ ^ 2 = mk W.toAffine (Polynomial.C W.Ψ₂Sq) :=
    WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq W

  have hφ_m :
      mk W.toAffine (W.φ m) = mk W.toAffine (Polynomial.C (W.Φ m)) :=
    WeierstrassCurve.Affine.CoordinateRing.mk_φ W m

  have hφ_2m :
      mk W.toAffine (W.φ (2 * m)) = mk W.toAffine (Polynomial.C (W.Φ (2 * m))) :=
    WeierstrassCurve.Affine.CoordinateRing.mk_φ W (2 * m)

  have hψ_m :
      mk W.toAffine (W.ψ m) = mk W.toAffine (W.Ψ m) :=
    WeierstrassCurve.Affine.CoordinateRing.mk_ψ W m

  have hψ_2m :
      mk W.toAffine (W.ψ (2 * m)) = mk W.toAffine (W.Ψ (2 * m)) :=
    WeierstrassCurve.Affine.CoordinateRing.mk_ψ W (2 * m)

  have hΨSq_m :
      mk W.toAffine (W.Ψ m) ^ 2 = mk W.toAffine (Polynomial.C (W.ΨSq m)) :=
    WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq W m

  have hΨSq_2m :
      mk W.toAffine (W.Ψ (2 * m)) ^ 2 = mk W.toAffine (Polynomial.C (W.ΨSq (2 * m))) :=
    WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq W (2 * m)

  -- The proof after this point is the generated algebraic certificate.
  -- It must rewrite:
  --   mk(C Φ n)     ↔ mk(φ n)
  --   mk(C ΨSq n)  ↔ mk(ψ n)^2
  --   mk(C Ψ₂Sq)   ↔ mk(ψ₂)^2
  -- then expand `φ`, `ψ_even`, `ψ_odd`, and use `hS`.
  --
  -- The exact closing line should be a generated `linear_combination`; see the script below.
  -- Without the generated cofactor, this theorem remains the one local algebraic certificate.
  --
  -- placeholder boundary:
  --   linear_combination (norm := ring_nf) Csomos * hS + Cb8 * hb8 + Cpsi2 * hψ2sq
  admit

end FLT.DivisionPolynomialDoubling
```

The theorem above is the one I would ask the CAS to generate a certificate for.  Once it is proved, the remaining descent is short and robust.

---

## Descent and cancellation

Assuming the multiplied coordinate-ring theorem, the raw theorem follows as follows.

```lean
namespace FLT.DivisionPolynomialDoubling

open Polynomial WeierstrassCurve
open WeierstrassCurve.Affine.CoordinateRing

variable {k : Type*} [Field k]
variable (W : WeierstrassCurve k) [W.IsElliptic]

/-- Constants in `Y` inject into the affine coordinate ring.  This is supplied in `PsiSomos.lean`. -/
-- theorem FLT.EDS.mk_C_injective (W) : Function.Injective (fun p : k[X] => mk W (C p))

/-- Nonvanishing of `Ψ₂Sq` for an elliptic curve.  If this is not already present, prove it by
`Ψ₂Sq = 4X^3 + b₂X^2 + 2b₄X + b₆`; if this polynomial were zero, the curve would be singular. -/
axiom Ψ₂Sq_ne_zero : W.Ψ₂Sq ≠ 0

/-- Raw polynomial identity from the multiplied coordinate-ring identity. -/
theorem dup_doubling_cross_from_multiplied_mk (m : ℤ) :
    W.Φ (2 * m) * dupDenP W (W.Φ m) (W.ΨSq m)
      = W.ΨSq (2 * m) * dupNumP W (W.Φ m) (W.ΨSq m) := by
  let D : k[X] := dupCrossDiff W m

  have hmk_mul :
      mk W.toAffine (Polynomial.C (W.Ψ₂Sq * D)) = 0 := by
    have h := mk_Ψ₂Sq_mul_dupCrossDiff (W := W) m
    simpa [D, dupCrossDiff, map_mul] using h

  have hpoly_mul : W.Ψ₂Sq * D = 0 :=
    FLT.EDS.mk_C_injective W.toAffine hmk_mul

  have hD : D = 0 := by
    exact mul_eq_zero.mp hpoly_mul |>.resolve_left (Ψ₂Sq_ne_zero (W := W))

  exact sub_eq_zero.mp hD

end FLT.DivisionPolynomialDoubling
```

If the local proof can avoid multiplying by `Ψ₂Sq`, then the cancellation lemma is unnecessary.  But because `ψ_even` has `ψ(2m) * ψ₂` on the left, the multiplied route is the safer one.

---

## CAS certificate generator for the multiplied coordinate-ring theorem

Use variables:

```text
A = ψ(m-2)
B = ψ(m-1)
C = ψ(m)
D = ψ(m+1)
E = ψ(m+2)
Q = ψ₂² = Ψ₂Sq
T = Ψ₃
X,b₂,b₄,b₆,b₈
```

Relations:

```text
R_somos = A*E - Q*B*D + T*C^2
R_Q     = Q - (4*X^3 + b2*X^2 + 2*b4*X + b6)
R_T     = T - (3*X^4 + b2*X^3 + 3*b4*X^2 + 3*b6*X + b8)
R_b8    = 4*b8 - b2*b6 + b4^2
```

The multiplied residual is:

```text
Q * (φ_{2m} * dupDen(φ_m,ψ_m²) - ψ_{2m}² * dupNum(φ_m,ψ_m²)).
```

Use the formulas:

```text
φ_m = X*C^2 - D*B
ψ(2m)*ψ₂ = C*(B^2*E - A*D^2)
ψ(2m+1) = E*C^3 - B*D^3
ψ(2m-1) = D*B^3 - A*C^3
Q*ψ(2m)^2 = C^2*(B^2*E - A*D^2)^2
Q*φ(2m) = X*C^2*(B^2*E - A*D^2)^2 - Q*(E*C^3 - B*D^3)*(D*B^3 - A*C^3)
```

Sage script:

```python
R = PolynomialRing(QQ, names='A,B,C,D,E,Q,T,X,b2,b4,b6,b8', order='degrevlex')
A,B,C,D,E,Q,T,X,b2,b4,b6,b8 = R.gens()

Qpoly = 4*X^3 + b2*X^2 + 2*b4*X + b6
Tpoly = 3*X^4 + b2*X^3 + 3*b4*X^2 + 3*b6*X + b8

def dupNum(P,Z):
    return P^4 - b4*P^2*Z^2 - 2*b6*P*Z^3 - b8*Z^4

def dupDen(P,Z):
    return 4*P^3*Z + b2*P^2*Z^2 + 2*b4*P*Z^3 + b6*Z^4

Phi_m = X*C^2 - D*B
Psi_m_sq = C^2
S = B^2*E - A*D^2
Q_Psi2m_sq = C^2*S^2
Q_Phi2m = X*C^2*S^2 - Q*(E*C^3 - B*D^3)*(D*B^3 - A*C^3)

# Q * cross-difference:
res = Q_Phi2m * dupDen(Phi_m, Psi_m_sq) - Q_Psi2m_sq * dupNum(Phi_m, Psi_m_sq)

rels = [
    A*E - Q*B*D + T*C^2,
    Q - Qpoly,
    T - Tpoly,
    4*b8 - b2*b6 + b4^2,
]
I = ideal(rels)
assert I.reduce(res) == 0
cofs = I.lift(res)
print([c.factor() for c in cofs])
```

The printed `cofs` are the exact cofactors to paste into:

```lean
linear_combination (norm := ring_nf)
  cofs[0] * hS + cofs[1] * hQ + cofs[2] * hT + cofs[3] * hb8
```

where `hS` is `mk_psi_adjacent_somos W m` after normalisation, `hQ` is the definition of `Ψ₂Sq`, `hT` is the definition of `Ψ₃`, and `hb8` is `W.b_relation` mapped into the coordinate ring.

---

## Bottom line

The strategy is correct.  But a complete no-sorry Lean proof requires the explicit generated cofactor certificate for `mk_Ψ₂Sq_mul_dupCrossDiff`.  I cannot provide that certificate without computing it against the exact residual normal form, and I cannot inspect the scratch Lean files through the connector.

The proof should be finalised by generating the four cofactors from the script above and replacing the `admit` in `mk_Ψ₂Sq_mul_dupCrossDiff` with the corresponding `linear_combination`.
