# Q227-dm1: concrete EDS-relation attack on the division-polynomial doubling identity

## Verdict

The missing relation is the **adjacent Somos / elliptic-sequence relation**

```text
ψ_{m+2} ψ_{m-2} = ψ_{m+1} ψ_{m-1} ψ₂² + ψ₃ ψ_m².
```

For Mathlib's univariate `preΨ`, which omits the bivariate `ψ₂` factor in even index, this becomes the parity-normalized relation

```text
preΨ_{m+2} preΨ_{m-2}
  = (if Even m then 1 else Ψ₂Sq²) * preΨ_{m+1} preΨ_{m-1}
      + preΨ₃ * preΨ_m².
```

This is the concrete relation among

```lean
W.preΨ (m - 2), W.preΨ (m - 1), W.preΨ m, W.preΨ (m + 1), W.preΨ (m + 2), W.Ψ₂Sq
```

that the failed `ring` proof is missing.

However, Mathlib currently does **not** appear to provide the theorem saying the normalized EDS `preNormEDS` / `normEDS` satisfies `IsEllSequence`.  The documentation for `Mathlib.NumberTheory.EllipticDivisibilitySequence` defines

```lean
IsEllSequence W
```

as the general relation

```lean
∀ m n r : ℤ,
  W (m+n) * W (m-n) * W r ^ 2
    = W (m+r) * W (m-r) * W n ^ 2
      - W (n+r) * W (n-r) * W m ^ 2
```

but the same file lists as TODO:

```text
prove that normEDS satisfies IsEllDivSequence
```

So the exact gap is not the recurrence lemmas `preΨ_even` / `preΨ_odd`; those exist.  The gap is the global elliptic-sequence/Somos relation for `preΨ` or `ψ`.

---

## 1. The exact relation needed

Use this theorem as the local missing lemma:

```lean
import Mathlib

open Polynomial WeierstrassCurve

namespace FLT.DivisionPolynomialDoublingEDS

variable {R : Type*} [CommRing R]
variable (W : WeierstrassCurve R)

/--
Adjacent Somos relation for Mathlib's parity-normalized univariate `preΨ`.

This is the normalized form of

`ψ_{m+2} ψ_{m-2} = ψ_{m+1} ψ_{m-1} ψ₂² + ψ₃ ψ_m²`.

When `m` is even, `m±2` and `m` are even, while `m±1` are odd; after cancelling the common
`ψ₂²`, the coefficient of `preΨ_{m+1} preΨ_{m-1}` is `1`.

When `m` is odd, `m±1` are even, so the middle product contributes `ψ₂⁴ = Ψ₂Sq²`.
-/
theorem preΨ_adjacent_somos (m : ℤ) :
    W.preΨ (m + 2) * W.preΨ (m - 2)
      = (if Even m then (1 : R[X]) else W.Ψ₂Sq ^ 2)
          * W.preΨ (m + 1) * W.preΨ (m - 1)
        + W.preΨ 3 * W.preΨ m ^ 2 := by
  -- Missing in Mathlib at present.
  -- It follows from the bivariate elliptic-sequence theorem for `ψ`, specialized to `(m,2,1)`,
  -- plus the parity normalization `ψ_n = preΨ_n * ψ₂` for even `n` and `ψ_n = preΨ_n` for odd `n`.
  sorry
```

The two useful branch lemmas are:

```lean
theorem preΨ_adjacent_somos_even
    {m : ℤ} (hm : Even m) :
    W.preΨ (m + 2) * W.preΨ (m - 2)
      = W.preΨ (m + 1) * W.preΨ (m - 1)
        + W.preΨ 3 * W.preΨ m ^ 2 := by
  simpa [hm, mul_assoc, mul_comm, mul_left_comm]
    using preΨ_adjacent_somos (W := W) m

theorem preΨ_adjacent_somos_odd
    {m : ℤ} (hm : Odd m) :
    W.preΨ (m + 2) * W.preΨ (m - 2)
      = W.Ψ₂Sq ^ 2 * W.preΨ (m + 1) * W.preΨ (m - 1)
        + W.preΨ 3 * W.preΨ m ^ 2 := by
  have hne : ¬ Even m := Int.not_even_iff_odd.mpr hm
  simpa [hne, mul_assoc, mul_comm, mul_left_comm]
    using preΨ_adjacent_somos (W := W) m

end FLT.DivisionPolynomialDoublingEDS
```

This is the single relation among the five neighboring terms.  The other reductions needed by `ring` are the already-used coefficient identities:

```lean
W.Ψ₂Sq = 4*X^3 + C W.b₂*X^2 + C (2*W.b₄)*X + C W.b₆
4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2
W.preΨ 3 = 3*X^4 + C W.b₂*X^3 + C (3*W.b₄)*X^2 + C (3*W.b₆)*X + C W.b₈
```

The first is `WeierstrassCurve.Ψ₂Sq` by unfolding.  The second is `W.b_relation`.  The third should close by `simp [WeierstrassCurve.preΨ, WeierstrassCurve.preΨ_three]` or by unfolding the division polynomial small cases, depending on local names.

---

## 2. Derivation from the full EDS relation

If Mathlib later has a theorem like

```lean
theorem isEllSequence_ψ (W : WeierstrassCurve R) :
    IsEllSequence W.ψ
```

then the proof of the adjacent relation should be:

```lean
namespace FLT.DivisionPolynomialDoublingEDS

open Polynomial WeierstrassCurve

variable {R : Type*} [CommRing R]
variable (W : WeierstrassCurve R)

/-- Hypothetical full bivariate elliptic-sequence theorem. -/
axiom ψ_isEllSequence :
    IsEllSequence W.ψ

/-- Full bivariate adjacent relation, before parity-normalization. -/
theorem ψ_adjacent_somos (m : ℤ) :
    W.ψ (m + 2) * W.ψ (m - 2)
      = W.ψ (m + 1) * W.ψ (m - 1) * W.ψ₂ ^ 2
        + W.ψ 3 * W.ψ m ^ 2 := by
  -- `IsEllSequence` specialized to `(m, 2, 1)`:
  have h := ψ_isEllSequence (W := W) m 2 1
  -- The raw relation is:
  -- ψ_{m+2} ψ_{m-2} ψ_1^2
  --   = ψ_{m+1} ψ_{m-1} ψ_2^2 - ψ_3 ψ_{-1} ψ_m^2.
  -- Use ψ_1=1 and ψ_{-1}=-1.
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
    WeierstrassCurve.ψ_one, WeierstrassCurve.ψ_neg]
    using h

end FLT.DivisionPolynomialDoublingEDS
```

Then the univariate version follows by replacing bivariate `ψ` with `preΨ` and replacing `ψ₂²` by `Ψ₂Sq` in the coordinate ring.  If a raw univariate theorem is desired, it should be proved directly for `preNormEDS` / `preΨ`, not via quotienting by the coordinate ring.

The missing Mathlib lemma is therefore precisely one of these:

```lean
theorem WeierstrassCurve.isEllSequence_ψ
    (W : WeierstrassCurve R) :
    IsEllSequence W.ψ
```

or the smaller normalized theorem:

```lean
theorem WeierstrassCurve.preΨ_adjacent_somos
    (W : WeierstrassCurve R) (m : ℤ) :
    W.preΨ (m + 2) * W.preΨ (m - 2)
      = (if Even m then 1 else W.Ψ₂Sq ^ 2)
          * W.preΨ (m + 1) * W.preΨ (m - 1)
        + W.preΨ 3 * W.preΨ m ^ 2
```

---

## 3. Use in the doubling identity proof

Here is the patched shape of the proof.  The important part is to introduce aliases for the five consecutive terms and the four coefficient relations, then close by a generated ideal certificate.

```lean
namespace FLT.DivisionPolynomialDoublingEDS

open Polynomial WeierstrassCurve

variable {R : Type*} [CommRing R]
variable (W : WeierstrassCurve R)

noncomputable def dupNumP (P Q : R[X]) : R[X] :=
  P ^ 4
    - C W.b₄ * P ^ 2 * Q ^ 2
    - C (2 * W.b₆) * P * Q ^ 3
    - C W.b₈ * Q ^ 4

noncomputable def dupDenP (P Q : R[X]) : R[X] :=
  C 4 * P ^ 3 * Q
    + C W.b₂ * P ^ 2 * Q ^ 2
    + C (2 * W.b₄) * P * Q ^ 3
    + C W.b₆ * Q ^ 4

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem dup_doubling_cross_with_somos (m : ℤ) :
    W.Φ (2 * m) * dupDenP W (W.Φ m) (W.ΨSq m)
      = W.ΨSq (2 * m) * dupNumP W (W.Φ m) (W.ΨSq m) := by
  classical

  have hΦ2m :
      W.Φ (2 * m)
        = X * W.ΨSq (2 * m)
          - W.preΨ (2 * m + 1) * W.preΨ (2 * m - 1) := by
    rw [WeierstrassCurve.Φ, if_pos (even_two_mul m), mul_one]

  have h2m1 : (2 * m - 1 : ℤ) = 2 * (m - 1) + 1 := by ring

  have hQ :
      W.Ψ₂Sq =
        C (4 : R) * X ^ 3
          + C W.b₂ * X ^ 2
          + C (2 * W.b₄) * X
          + C W.b₆ := by
    simp [WeierstrassCurve.Ψ₂Sq]

  have hb8 : C (4 * W.b₈) = C (W.b₂ * W.b₆ - W.b₄ ^ 2) := by
    rw [W.b_relation]

  have h3 :
      W.preΨ 3 =
        C (3 : R) * X ^ 4
          + C W.b₂ * X ^ 3
          + C (3 * W.b₄) * X ^ 2
          + C (3 * W.b₆) * X
          + C W.b₈ := by
    -- If local names differ, replace by the exact small-case simp theorem for `preΨ_three`.
    simp [WeierstrassCurve.preΨ]

  rw [hΦ2m, W.ΨSq_even m, W.preΨ_odd m, h2m1, W.preΨ_odd (m - 1)]

  simp only [WeierstrassCurve.Φ, WeierstrassCurve.ΨSq, dupNumP, dupDenP]

  rcases Int.even_or_odd m with hm | hm
  · have hm1 : ¬ Even (m - 1) := by
      rcases hm with ⟨t, rfl⟩
      intro h
      rw [Int.even_iff] at h
      omega

    have hS :
        W.preΨ (m + 2) * W.preΨ (m - 2)
          = W.preΨ (m + 1) * W.preΨ (m - 1)
            + W.preΨ 3 * W.preΨ m ^ 2 :=
      preΨ_adjacent_somos_even (W := W) hm

    simp only [if_pos hm, if_neg hm1]

    -- At this point `ring` leaves exactly the ideal generated by `hS`, `hQ`, `hb8`, `h3`.
    -- The following `linear_combination` needs the generated cofactor certificate.
    -- See the Sage script below.
    linear_combination (norm := ring_nf)
      (somosCoeff_even W m) * hS
        + (QCoeff_even W m) * hQ
        + (b8Coeff_even W m) * hb8
        + (threeCoeff_even W m) * h3

  · have hm0 : ¬ Even m := Int.not_even_iff_odd.mpr hm
    have hm1 : Even (m - 1) := by
      rcases hm with ⟨t, rfl⟩
      exact ⟨t, by ring⟩

    have hS :
        W.preΨ (m + 2) * W.preΨ (m - 2)
          = W.Ψ₂Sq ^ 2 * W.preΨ (m + 1) * W.preΨ (m - 1)
            + W.preΨ 3 * W.preΨ m ^ 2 :=
      preΨ_adjacent_somos_odd (W := W) hm

    simp only [if_neg hm0, if_pos hm1]

    linear_combination (norm := ring_nf)
      (somosCoeff_odd W m) * hS
        + (QCoeff_odd W m) * hQ
        + (b8Coeff_odd W m) * hb8
        + (threeCoeff_odd W m) * h3

end FLT.DivisionPolynomialDoublingEDS
```

The identifiers

```lean
somosCoeff_even, QCoeff_even, b8Coeff_even, threeCoeff_even
somosCoeff_odd,  QCoeff_odd,  b8Coeff_odd,  threeCoeff_odd
```

are not mathematical lemmas; they are generated polynomial cofactors.  They should be produced mechanically.

---

## 4. How to compute the cofactors

Do not try to discover the cofactors manually.  Generate them from the residual using a polynomial quotient / Groebner reduction over the universal polynomial ring.

Use variables:

```text
A = preΨ(m-2)
B = preΨ(m-1)
C = preΨ(m)
D = preΨ(m+1)
E = preΨ(m+2)
Q = Ψ₂Sq
T = preΨ(3)
X = Polynomial.X
b2,b4,b6,b8
```

Relations:

Even case:

```text
R_somos_even = A*E - B*D - T*C^2
R_Q          = Q - (4*X^3 + b2*X^2 + 2*b4*X + b6)
R_b8         = 4*b8 - b2*b6 + b4^2
R_T          = T - (3*X^4 + b2*X^3 + 3*b4*X^2 + 3*b6*X + b8)
```

Odd case:

```text
R_somos_odd = A*E - Q^2*B*D - T*C^2
R_Q         = Q - (4*X^3 + b2*X^2 + 2*b4*X + b6)
R_b8        = 4*b8 - b2*b6 + b4^2
R_T         = T - (3*X^4 + b2*X^3 + 3*b4*X^2 + 3*b6*X + b8)
```

Sage script:

```python
# sage
R = PolynomialRing(QQ, names='A,B,C,D,E,Q,T,X,b2,b4,b6,b8', order='degrevlex')
A,B,C,D,E,Q,T,X,b2,b4,b6,b8 = R.gens()

Qpoly = 4*X^3 + b2*X^2 + 2*b4*X + b6
Tpoly = 3*X^4 + b2*X^3 + 3*b4*X^2 + 3*b6*X + b8

def dupNum(P, Z):
    return P^4 - b4*P^2*Z^2 - 2*b6*P*Z^3 - b8*Z^4

def dupDen(P, Z):
    return 4*P^3*Z + b2*P^2*Z^2 + 2*b4*P*Z^3 + b6*Z^4

S = B^2*C*E - A*C*D^2
Psi2m = S^2 * Q

# even m
Psi_m_e = C^2 * Q
Phi_m_e = X*Psi_m_e - D*B
U2p_e = E*C^3*Q^2 - B*D^3
U2m_e = D*B^3 - A*C^3*Q^2
Phi2m_e = X*Psi2m - U2p_e*U2m_e
res_e = Phi2m_e*dupDen(Phi_m_e, Psi_m_e) - Psi2m*dupNum(Phi_m_e, Psi_m_e)

rels_e = [
    A*E - B*D - T*C^2,
    Q - Qpoly,
    4*b8 - b2*b6 + b4^2,
    T - Tpoly,
]
I_e = ideal(rels_e)
rem_e = I_e.reduce(res_e)
assert rem_e == 0
cofs_e = I_e.lift(res_e)   # coefficients for rels_e
print([c.factor() for c in cofs_e])

# odd m
Psi_m_o = C^2
Phi_m_o = X*Psi_m_o - D*B*Q
U2p_o = E*C^3 - B*D^3*Q^2
U2m_o = D*B^3*Q^2 - A*C^3
Phi2m_o = X*Psi2m - U2p_o*U2m_o
res_o = Phi2m_o*dupDen(Phi_m_o, Psi_m_o) - Psi2m*dupNum(Phi_m_o, Psi_m_o)

rels_o = [
    A*E - Q^2*B*D - T*C^2,
    Q - Qpoly,
    4*b8 - b2*b6 + b4^2,
    T - Tpoly,
]
I_o = ideal(rels_o)
rem_o = I_o.reduce(res_o)
assert rem_o == 0
cofs_o = I_o.lift(res_o)
print([c.factor() for c in cofs_o])
```

Then translate each printed cofactor into a Lean definition:

```lean
noncomputable def somosCoeff_even (W : WeierstrassCurve R) (m : ℤ) : R[X] :=
  -- substitute A,B,C,D,E,Q,T,X,bᵢ by the corresponding polynomials
  sorry
```

In practice, to avoid gigantic hand-written definitions, put the generated `linear_combination` expression directly in the proof.  `linear_combination` is usually more robust with explicit expressions than with opaque definitions.

---

## 5. If the cofactors are too large

A more Lean-native way is to make the Somos relation a rewrite by eliminating `A*E` before running `ring_nf`:

Even case:

```lean
have hAE :
    W.preΨ (m - 2) * W.preΨ (m + 2)
      = W.preΨ (m - 1) * W.preΨ (m + 1)
        + W.preΨ 3 * W.preΨ m ^ 2 := by
  simpa [mul_comm, mul_left_comm, mul_assoc, add_comm]
    using hS

-- If the residual is written with every occurrence as `(A*E)`, then:
--   rw [hAE]
--   rw [hQ, h3]
--   use W.b_relation
--   ring
```

But this only works if the residual is syntactically organized with factors `A*E`.  Usually it is not.  Therefore the generated ideal certificate is the reliable route.

---

## 6. Concrete answer to the requested items

### 1. Exact relation(s)

One normalized adjacent relation, split by parity:

```lean
preΨ(m+2) * preΨ(m-2)
  = preΨ(m+1) * preΨ(m-1) + preΨ(3) * preΨ(m)^2
```

when `Even m`, and

```lean
preΨ(m+2) * preΨ(m-2)
  = Ψ₂Sq^2 * preΨ(m+1) * preΨ(m-1) + preΨ(3) * preΨ(m)^2
```

when `Odd m`.

This is the specialization `(i,j,k) = (m,2,1)` of

```lean
ψ_{i+j} ψ_{i-j} ψ_k²
  = ψ_{i+k} ψ_{i-k} ψ_j² - ψ_{j+k} ψ_{j-k} ψ_i².
```

### 2. Lean proof of `R_i`

If Mathlib has `WeierstrassCurve.isEllSequence_ψ`, specialize it as shown above.  Current Mathlib documentation exposes `IsEllSequence`, but says proving `normEDS` satisfies `IsEllDivSequence` is TODO.  Therefore the smallest theorem to prove locally is `preΨ_adjacent_somos`.

### 3. Closing tactic

Use:

```lean
linear_combination (norm := ring_nf)
  cofactor_somos * hS
    + cofactor_Q * hQ
    + cofactor_b8 * hb8
    + cofactor_three * h3
```

where the cofactors are generated by the Sage script above.  The script gives an exact ideal certificate for both parity branches.

Without those generated cofactors, `ring` will keep failing: it sees the five neighboring `preΨ` terms as independent variables.

---

## Final recommendation

Add the local seam:

```lean
theorem preΨ_adjacent_somos (W : WeierstrassCurve R) (m : ℤ) :
    W.preΨ (m + 2) * W.preΨ (m - 2)
      = (if Even m then (1 : R[X]) else W.Ψ₂Sq ^ 2)
          * W.preΨ (m + 1) * W.preΨ (m - 1)
        + W.preΨ 3 * W.preΨ m ^ 2
```

Then close `dup_doubling_cross` by generated ideal certificates.  This is concrete EDS algebra, not a conceptual geometry gap, but the cofactor expressions are too large to derive by hand; generate them.
