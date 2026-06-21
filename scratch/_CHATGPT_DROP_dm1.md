# Q-GITDROP-dm1: gcd cancellation bridge for duplication height lower bound

This is the clean way to isolate the gcd-cancellation step.  Do **not** prove it by inspecting the
special duplication polynomials directly.  Prove it from the two homogenized Bezout identities:

\[
D X^7 = U_x(X,Z) F(X,Z) + V_x(X,Z) G(X,Z),
\]

\[
D Z^7 = U_z(X,Z) F(X,Z) + V_z(X,Z) G(X,Z),
\]

where \(D=\Delta^2\).  Then for primitive \((X,Z)\), any common divisor of \(F(X,Z)\) and
\(G(X,Z)\) divides both \(D X^7\) and \(D Z^7\), hence divides \(D\), because
\(\gcd(X^7,Z^7)=1\).  This handles the degenerate branch \(G(X,Z)=0\) automatically: then
`Nat.gcd |F| 0 = |F|`, and the same two Bezout identities force `|F| ∣ |D|`.

The only API names I am not completely certain about in your checkout are the final wrapper from
`IsCoprime X Z` over `ℤ` to `Nat.Coprime X.natAbs Z.natAbs`, and the exact names for
`Nat.gcd_mul_left`/`Nat.Coprime.pow`.  The core proof below is written against stable Mathlib-style
lemmas and should need only local renaming if those declarations differ.

```lean
import Mathlib

namespace FLT.HeightDoubling.GcdCancellation

/--
A two-chart homogeneous Bezout certificate for the duplication forms.

For the elliptic-curve duplication application, `D = Δ^2`, `F = dupNumHZ`,
`G = dupDenHZ`, and the exponent is `7 = 2*4 - 1`.
-/
structure HomogeneousBezoutCertificate where
  F : ℤ → ℤ → ℤ
  G : ℤ → ℤ → ℤ
  D : ℤ
  Ux : ℤ → ℤ → ℤ
  Vx : ℤ → ℤ → ℤ
  Uz : ℤ → ℤ → ℤ
  Vz : ℤ → ℤ → ℤ
  bezoutX : ∀ X Z : ℤ,
    D * X ^ 7 = Ux X Z * F X Z + Vx X Z * G X Z
  bezoutZ : ∀ X Z : ℤ,
    D * Z ^ 7 = Uz X Z * F X Z + Vz X Z * G X Z

namespace HomogeneousBezoutCertificate

variable (C : HomogeneousBezoutCertificate)

/-- If a natural number divides the absolute values of two integers, then it divides
any integer linear combination, again after absolute value. -/
lemma dvd_natAbs_add_mul_of_dvd_natAbs
    {d : ℕ} {a b u v : ℤ}
    (ha : d ∣ a.natAbs) (hb : d ∣ b.natAbs) :
    d ∣ (u * a + v * b).natAbs := by
  -- The stable route is through integer divisibility.
  -- If your checkout has a different name, replace the two lines below by the
  -- equivalent `Int.dvd_iff_dvd_natAbs`/`Int.natAbs_dvd_natAbs` lemma.
  have haZ : (d : ℤ) ∣ a := by
    exact (Int.ofNat_dvd_left.mpr ha)
  have hbZ : (d : ℤ) ∣ b := by
    exact (Int.ofNat_dvd_left.mpr hb)
  have hlinZ : (d : ℤ) ∣ u * a + v * b := by
    exact dvd_add (dvd_mul_of_dvd_right haZ u) (dvd_mul_of_dvd_right hbZ v)
  exact Int.ofNat_dvd_left.mp hlinZ

/-- Main arithmetic lemma, stated with `Nat.Coprime` on absolute values.
This is the core proof used by the `IsCoprime X Z` wrapper. -/
theorem gcd_dvd_D_natAbs_of_natAbs_coprime
    {X Z : ℤ}
    (hcop : Nat.Coprime X.natAbs Z.natAbs) :
    Nat.gcd (C.F X Z).natAbs (C.G X Z).natAbs ∣ C.D.natAbs := by
  let d : ℕ := Nat.gcd (C.F X Z).natAbs (C.G X Z).natAbs

  have hdF : d ∣ (C.F X Z).natAbs := Nat.gcd_dvd_left _ _
  have hdG : d ∣ (C.G X Z).natAbs := Nat.gcd_dvd_right _ _

  have hd_comboX :
      d ∣ (C.Ux X Z * C.F X Z + C.Vx X Z * C.G X Z).natAbs :=
    dvd_natAbs_add_mul_of_dvd_natAbs hdF hdG

  have hd_comboZ :
      d ∣ (C.Uz X Z * C.F X Z + C.Vz X Z * C.G X Z).natAbs :=
    dvd_natAbs_add_mul_of_dvd_natAbs hdF hdG

  have hd_DX : d ∣ (C.D * X ^ 7).natAbs := by
    simpa [C.bezoutX X Z] using hd_comboX

  have hd_DZ : d ∣ (C.D * Z ^ 7).natAbs := by
    simpa [C.bezoutZ X Z] using hd_comboZ

  have hd_DX' : d ∣ C.D.natAbs * X.natAbs ^ 7 := by
    simpa [Int.natAbs_mul, Int.natAbs_pow] using hd_DX

  have hd_DZ' : d ∣ C.D.natAbs * Z.natAbs ^ 7 := by
    simpa [Int.natAbs_mul, Int.natAbs_pow] using hd_DZ

  have hpowcop : Nat.Coprime (X.natAbs ^ 7) (Z.natAbs ^ 7) := by
    exact hcop.pow 7 7

  have hd_gcd :
      d ∣ Nat.gcd (C.D.natAbs * X.natAbs ^ 7)
                   (C.D.natAbs * Z.natAbs ^ 7) :=
    Nat.dvd_gcd hd_DX' hd_DZ'

  -- `gcd (D*X^7) (D*Z^7) = D * gcd(X^7,Z^7) = D`.
  -- In some Mathlib versions the simp lemma is named `Nat.gcd_mul_left`; if not,
  -- use `rw [← Nat.mul_gcd_left]` or the local lemma below.
  have hgcd_eval :
      Nat.gcd (C.D.natAbs * X.natAbs ^ 7)
                   (C.D.natAbs * Z.natAbs ^ 7) = C.D.natAbs := by
    rw [← Nat.mul_gcd_left]
    rw [hpowcop.gcd_eq_one]
    simp

  simpa [hgcd_eval] using hd_gcd

/-- Wrapper with the statement shape requested in the height assembly.

If your local `IsCoprime` API over `ℤ` does not simplify to `Nat.Coprime X.natAbs Z.natAbs`,
replace the `hcopNat` proof by the corresponding lemma.  Common names are along the lines of
`Int.isCoprime_iff_natAbs_coprime` or `IsCoprime.natAbs` depending on the imported file set.
-/
theorem gcd_dvd_D_natAbs
    {X Z : ℤ}
    (hcop : IsCoprime X Z) :
    Nat.gcd (C.F X Z).natAbs (C.G X Z).natAbs ∣ C.D.natAbs := by
  have hcopNat : Nat.Coprime X.natAbs Z.natAbs := by
    -- API shim.  Replace by the exact theorem in the project if this simp does not fire.
    simpa [Int.natAbs_eq_natAbs, Int.isCoprime_iff_natAbs] using hcop
  exact C.gcd_dvd_D_natAbs_of_natAbs_coprime hcopNat

end HomogeneousBezoutCertificate

/-!
## How to build the certificate from the affine Bezout identity

Suppose the affine resultant certificate is:

```lean
pX * dupNumPoly + qX * dupDenPoly = Polynomial.C (Δ ^ 2)
```

for the `Z = 1` chart.  Homogenizing to total degree `7` gives

```lean
Δ^2 * Z^7 = U_Z(X,Z) * F(X,Z) + V_Z(X,Z) * G(X,Z)
```

where `U_Z,V_Z` are the degree-3 homogenizations of `pX,qX`.

For the `X = 1` chart, apply the same affine Bezout theorem to the reciprocal polynomials

```lean
Frev(T) = T^4 * F(1/T, 1) = F(1,T)
Grev(T) = T^4 * G(1/T, 1) = G(1,T)
```

and homogenize.  Evaluating that identity at `(Z,X)` gives

```lean
Δ^2 * X^7 = U_X(X,Z) * F(X,Z) + V_X(X,Z) * G(X,Z).
```

The exponent is `7` because the forms have degree `4`, and the Bezout cofactors have degree at most `3`;
hence the homogenized products have total degree `4 + 3 = 7`.
-/

/-- A tiny abstraction for a degree-3 integer binary form. -/
structure BinaryCubicZ where
  c0 : ℤ
  c1 : ℤ
  c2 : ℤ
  c3 : ℤ

def BinaryCubicZ.eval (A : BinaryCubicZ) (X Z : ℤ) : ℤ :=
  A.c0 * Z ^ 3 + A.c1 * X * Z ^ 2 + A.c2 * X ^ 2 * Z + A.c3 * X ^ 3

/-- Degree-4 homogeneous duplication-form package. -/
structure DupFormsZ where
  F : ℤ → ℤ → ℤ
  G : ℤ → ℤ → ℤ
  Δ : ℤ
  Ux : BinaryCubicZ
  Vx : BinaryCubicZ
  Uz : BinaryCubicZ
  Vz : BinaryCubicZ
  bezoutX : ∀ X Z : ℤ,
    Δ ^ 2 * X ^ 7 = Ux.eval X Z * F X Z + Vx.eval X Z * G X Z
  bezoutZ : ∀ X Z : ℤ,
    Δ ^ 2 * Z ^ 7 = Uz.eval X Z * F X Z + Vz.eval X Z * G X Z

namespace DupFormsZ

/-- Turn the concrete duplication-form package into the abstract certificate. -/
def toCertificate (D : DupFormsZ) : HomogeneousBezoutCertificate where
  F := D.F
  G := D.G
  D := D.Δ ^ 2
  Ux := fun X Z => D.Ux.eval X Z
  Vx := fun X Z => D.Vx.eval X Z
  Uz := fun X Z => D.Uz.eval X Z
  Vz := fun X Z => D.Vz.eval X Z
  bezoutX := D.bezoutX
  bezoutZ := D.bezoutZ

/-- The requested duplication gcd-cancellation theorem. -/
theorem dup_gcd_dvd_resultant
    (D : DupFormsZ)
    (X Z : ℤ)
    (hcop : IsCoprime X Z) :
    Nat.gcd (D.F X Z).natAbs (D.G X Z).natAbs ∣ (D.Δ ^ 2).natAbs := by
  exact D.toCertificate.gcd_dvd_D_natAbs hcop

/-- Same theorem with the more robust primitive-pair hypothesis. -/
theorem dup_gcd_dvd_resultant_natCoprime
    (D : DupFormsZ)
    (X Z : ℤ)
    (hcop : Nat.Coprime X.natAbs Z.natAbs) :
    Nat.gcd (D.F X Z).natAbs (D.G X Z).natAbs ∣ (D.Δ ^ 2).natAbs := by
  exact D.toCertificate.gcd_dvd_D_natAbs_of_natAbs_coprime hcop

end DupFormsZ

end FLT.HeightDoubling.GcdCancellation
```

## Notes for integrating with `dup_bezout_affine`

The affine certificate from `Polynomial.exists_mul_add_mul_eq_C_resultant` should be used twice.

```lean
-- Z = 1 chart:
--   pZ * dupNumPoly + qZ * dupDenPoly = C (Δ^2)
-- Homogenize to degree 7:
--   Δ^2 * Z^7 = Uz(X,Z) * F(X,Z) + Vz(X,Z) * G(X,Z)

-- X = 1 chart:
--   pX * dupNumRevPoly + qX * dupDenRevPoly = C (Δ^2)
-- Homogenize and swap variables:
--   Δ^2 * X^7 = Ux(X,Z) * F(X,Z) + Vx(X,Z) * G(X,Z)
```

The two small reusable polynomial lemmas are:

```lean
-- schematic
lemma homEval_mul
    {R : Type*} [CommSemiring R]
    {p q : Polynomial R} {d e : ℕ}
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ e)
    (X Z : R) :
    homEval (d + e) (p * q) X Z = homEval d p X Z * homEval e q X Z := by
  -- coefficient convolution
  sorry

lemma homEval_C
    {R : Type*} [CommSemiring R]
    (a : R) (d : ℕ) (X Z : R) :
    homEval d (Polynomial.C a) X Z = a * Z ^ d := by
  -- direct from the definition of `homEval`
  sorry
```

Once those two chart identities are in the `DupFormsZ` structure, the gcd cancellation theorem above is the
complete final bridge.  The proof does not require `G X Z ≠ 0`; the `G=0` two-torsion direction is included because
`Nat.gcd |F| 0` still divides both Bezout right-hand sides.
