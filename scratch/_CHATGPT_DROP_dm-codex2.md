# Q2384 (dm-codex2): finite 2-adic full-cover obstruction certificates

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- A residue class is nonzero modulo the prime `p`, represented by `Fin m`. -/
def residueUnitAtPrime (p : Nat) {m : Nat} (a : Fin m) : Prop :=
  a.val % p ≠ 0

/-- The primitive projective condition for four residue variables. -/
def primitiveResidue4 (p : Nat) {m : Nat} (A B C T : Fin m) : Prop :=
  residueUnitAtPrime p A ∨ residueUnitAtPrime p B ∨
    residueUnitAtPrime p C ∨ residueUnitAtPrime p T

/-- The square residue of a residue variable, still represented in `Fin m`. -/
def sqResidueFin {m : Nat} (a : Fin m) : Fin m :=
  ⟨(a.val * a.val) % m, by
    have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le a.val) a.isLt
    exact Nat.mod_lt _ hm⟩

/-- A residue known to be a square modulo `m`. -/
def IsSquareResidue {m : Nat} (a2 : Fin m) : Prop :=
  ∃ a : Fin m, sqResidueFin a = a2

instance instDecidableIsSquareResidue {m : Nat} (a2 : Fin m) :
    Decidable (IsSquareResidue a2) := by
  unfold IsSquareResidue
  infer_instance

/-- The finite type of square residues modulo `m`.  For `m = 4, 8, 16` this is
much smaller than all residues. -/
abbrev SqResidue (m : Nat) := {a2 : Fin m // IsSquareResidue a2}

/-- The cover equations after replacing each variable by its square residue.

This is the fast checker used by the generated certificates. -/
def coverSquareResidue (m : Nat) (d0 d1 d3 : ℤ)
    (A2 B2 C2 T2 : Fin m) : Prop :=
  ((d0 * (A2.val : ℤ) - d1 * (B2.val : ℤ) - (T2.val : ℤ)) % (m : ℤ) = 0) ∧
  ((d3 * (C2.val : ℤ) - d0 * (A2.val : ℤ) - (3 : ℤ) * (T2.val : ℤ)) %
      (m : ℤ) = 0)

/-- The original cover equations over residue variables, implemented via their
square residues. -/
def coverResidue (m : Nat) (d0 d1 d3 : ℤ) (A B C T : Fin m) : Prop :=
  coverSquareResidue m d0 d1 d3
    (sqResidueFin A) (sqResidueFin B) (sqResidueFin C) (sqResidueFin T)

/-- Primitive condition on square residues.  For the moduli below, primitive
variables transfer to primitive square residues because `p = 2`. -/
def primitiveSquareResidue4 (p : Nat) {m : Nat} (A2 B2 C2 T2 : Fin m) : Prop :=
  residueUnitAtPrime p A2 ∨ residueUnitAtPrime p B2 ∨
    residueUnitAtPrime p C2 ∨ residueUnitAtPrime p T2

/-- No primitive solution to the cover equations modulo `m`. -/
def noPrimitiveCoverResidue (p m : Nat) (d0 d1 d3 : ℤ) : Prop :=
  ¬ ∃ A B C T : Fin m,
      primitiveResidue4 p A B C T ∧ coverResidue m d0 d1 d3 A B C T

/-- Fast square-residue-only version. -/
def noPrimitiveCoverResidueBySquares (p m : Nat) (d0 d1 d3 : ℤ) : Prop :=
  ¬ ∃ A2 B2 C2 T2 : SqResidue m,
      primitiveSquareResidue4 p A2.1 B2.1 C2.1 T2.1 ∧
        coverSquareResidue m d0 d1 d3 A2.1 B2.1 C2.1 T2.1

/-- A small transfer property: a variable nonzero mod `p` has square residue
nonzero mod `p`.  We prove it below by `native_decide` for `p=2` and
`m=4,8,16`. -/
def squarePrimitiveTransfer (p m : Nat) : Prop :=
  ∀ A : Fin m, residueUnitAtPrime p A → residueUnitAtPrime p (sqResidueFin A)

/-- Transfer from the square-residue certificate back to the original variables. -/
theorem noPrimitiveCoverResidue_of_noPrimitiveCoverResidueBySquares
    {p m : Nat} {d0 d1 d3 : ℤ}
    (hprimSq : squarePrimitiveTransfer p m)
    (hsq : noPrimitiveCoverResidueBySquares p m d0 d1 d3) :
    noPrimitiveCoverResidue p m d0 d1 d3 := by
  intro hbad
  rcases hbad with ⟨A, B, C, T, hprim, hcover⟩
  change coverSquareResidue m d0 d1 d3
      (sqResidueFin A) (sqResidueFin B) (sqResidueFin C) (sqResidueFin T) at hcover
  have hprim' : primitiveSquareResidue4 p
      (sqResidueFin A) (sqResidueFin B) (sqResidueFin C) (sqResidueFin T) := by
    rcases hprim with hA | hB | hC | hT
    · exact Or.inl (hprimSq A hA)
    · exact Or.inr (Or.inl (hprimSq B hB))
    · exact Or.inr (Or.inr (Or.inl (hprimSq C hC)))
    · exact Or.inr (Or.inr (Or.inr (hprimSq T hT)))
  exact hsq ⟨⟨sqResidueFin A, ⟨A, rfl⟩⟩,
    ⟨sqResidueFin B, ⟨B, rfl⟩⟩,
    ⟨sqResidueFin C, ⟨C, rfl⟩⟩,
    ⟨sqResidueFin T, ⟨T, rfl⟩⟩,
    hprim', hcover⟩

private theorem squarePrimitiveTransfer_2_mod4 :
    squarePrimitiveTransfer 2 4 := by
  native_decide

private theorem squarePrimitiveTransfer_2_mod8 :
    squarePrimitiveTransfer 2 8 := by
  native_decide

private theorem squarePrimitiveTransfer_2_mod16 :
    squarePrimitiveTransfer 2 16 := by
  native_decide

private theorem noPrimitiveCoverResidue_of_square_check_mod4 {d0 d1 d3 : ℤ}
    (h : noPrimitiveCoverResidueBySquares 2 4 d0 d1 d3) :
    noPrimitiveCoverResidue 2 4 d0 d1 d3 := by
  exact noPrimitiveCoverResidue_of_noPrimitiveCoverResidueBySquares
    (p := 2) (m := 4) (d0 := d0) (d1 := d1) (d3 := d3)
    squarePrimitiveTransfer_2_mod4 h

private theorem noPrimitiveCoverResidue_of_square_check_mod8 {d0 d1 d3 : ℤ}
    (h : noPrimitiveCoverResidueBySquares 2 8 d0 d1 d3) :
    noPrimitiveCoverResidue 2 8 d0 d1 d3 := by
  exact noPrimitiveCoverResidue_of_noPrimitiveCoverResidueBySquares
    (p := 2) (m := 8) (d0 := d0) (d1 := d1) (d3 := d3)
    squarePrimitiveTransfer_2_mod8 h

private theorem noPrimitiveCoverResidue_of_square_check_mod16 {d0 d1 d3 : ℤ}
    (h : noPrimitiveCoverResidueBySquares 2 16 d0 d1 d3) :
    noPrimitiveCoverResidue 2 16 d0 d1 d3 := by
  exact noPrimitiveCoverResidue_of_noPrimitiveCoverResidueBySquares
    (p := 2) (m := 16) (d0 := d0) (d1 := d1) (d3 := d3)
    squarePrimitiveTransfer_2_mod16 h

/-- `(1,2,2)`, killed modulo `8`. -/
theorem noPrimitiveCoverResidue_1_2_2_mod8 :
    noPrimitiveCoverResidue 2 8 (1 : ℤ) (2 : ℤ) (2 : ℤ) := by
  exact noPrimitiveCoverResidue_of_square_check_mod8
    (d0 := (1 : ℤ)) (d1 := (2 : ℤ)) (d3 := (2 : ℤ)) (by native_decide)

/-- `(1,3,3)`, killed modulo `16`. -/
theorem noPrimitiveCoverResidue_1_3_3_mod16 :
    noPrimitiveCoverResidue 2 16 (1 : ℤ) (3 : ℤ) (3 : ℤ) := by
  exact noPrimitiveCoverResidue_of_square_check_mod16
    (d0 := (1 : ℤ)) (d1 := (3 : ℤ)) (d3 := (3 : ℤ)) (by native_decide)

/-- `(1,6,6)`, killed modulo `8`. -/
theorem noPrimitiveCoverResidue_1_6_6_mod8 :
    noPrimitiveCoverResidue 2 8 (1 : ℤ) (6 : ℤ) (6 : ℤ) := by
  exact noPrimitiveCoverResidue_of_square_check_mod8
    (d0 := (1 : ℤ)) (d1 := (6 : ℤ)) (d3 := (6 : ℤ)) (by native_decide)

/-- `(2,1,2)`, killed modulo `4`. -/
theorem noPrimitiveCoverResidue_2_1_2_mod4 :
    noPrimitiveCoverResidue 2 4 (2 : ℤ) (1 : ℤ) (2 : ℤ) := by
  exact noPrimitiveCoverResidue_of_square_check_mod4
    (d0 := (2 : ℤ)) (d1 := (1 : ℤ)) (d3 := (2 : ℤ)) (by native_decide)

/-- `(2,2,1)`, killed modulo `4`. -/
theorem noPrimitiveCoverResidue_2_2_1_mod4 :
    noPrimitiveCoverResidue 2 4 (2 : ℤ) (2 : ℤ) (1 : ℤ) := by
  exact noPrimitiveCoverResidue_of_square_check_mod4
    (d0 := (2 : ℤ)) (d1 := (2 : ℤ)) (d3 := (1 : ℤ)) (by native_decide)

/-- `(2,3,6)`, killed modulo `4`. -/
theorem noPrimitiveCoverResidue_2_3_6_mod4 :
    noPrimitiveCoverResidue 2 4 (2 : ℤ) (3 : ℤ) (6 : ℤ) := by
  exact noPrimitiveCoverResidue_of_square_check_mod4
    (d0 := (2 : ℤ)) (d1 := (3 : ℤ)) (d3 := (6 : ℤ)) (by native_decide)

/-- `(2,6,3)`, killed modulo `4`. -/
theorem noPrimitiveCoverResidue_2_6_3_mod4 :
    noPrimitiveCoverResidue 2 4 (2 : ℤ) (6 : ℤ) (3 : ℤ) := by
  exact noPrimitiveCoverResidue_of_square_check_mod4
    (d0 := (2 : ℤ)) (d1 := (6 : ℤ)) (d3 := (3 : ℤ)) (by native_decide)

/-- `(3,1,3)`, killed modulo `4`. -/
theorem noPrimitiveCoverResidue_3_1_3_mod4 :
    noPrimitiveCoverResidue 2 4 (3 : ℤ) (1 : ℤ) (3 : ℤ) := by
  exact noPrimitiveCoverResidue_of_square_check_mod4
    (d0 := (3 : ℤ)) (d1 := (1 : ℤ)) (d3 := (3 : ℤ)) (by native_decide)

/-- `(3,3,1)`, killed modulo `4`. -/
theorem noPrimitiveCoverResidue_3_3_1_mod4 :
    noPrimitiveCoverResidue 2 4 (3 : ℤ) (3 : ℤ) (1 : ℤ) := by
  exact noPrimitiveCoverResidue_of_square_check_mod4
    (d0 := (3 : ℤ)) (d1 := (3 : ℤ)) (d3 := (1 : ℤ)) (by native_decide)

/-- `(3,6,2)`, killed modulo `8`. -/
theorem noPrimitiveCoverResidue_3_6_2_mod8 :
    noPrimitiveCoverResidue 2 8 (3 : ℤ) (6 : ℤ) (2 : ℤ) := by
  exact noPrimitiveCoverResidue_of_square_check_mod8
    (d0 := (3 : ℤ)) (d1 := (6 : ℤ)) (d3 := (2 : ℤ)) (by native_decide)

/-- `(6,1,6)`, killed modulo `4`. -/
theorem noPrimitiveCoverResidue_6_1_6_mod4 :
    noPrimitiveCoverResidue 2 4 (6 : ℤ) (1 : ℤ) (6 : ℤ) := by
  exact noPrimitiveCoverResidue_of_square_check_mod4
    (d0 := (6 : ℤ)) (d1 := (1 : ℤ)) (d3 := (6 : ℤ)) (by native_decide)

/-- `(6,2,3)`, killed modulo `4`. -/
theorem noPrimitiveCoverResidue_6_2_3_mod4 :
    noPrimitiveCoverResidue 2 4 (6 : ℤ) (2 : ℤ) (3 : ℤ) := by
  exact noPrimitiveCoverResidue_of_square_check_mod4
    (d0 := (6 : ℤ)) (d1 := (2 : ℤ)) (d3 := (3 : ℤ)) (by native_decide)

/-- `(6,3,2)`, killed modulo `4`. -/
theorem noPrimitiveCoverResidue_6_3_2_mod4 :
    noPrimitiveCoverResidue 2 4 (6 : ℤ) (3 : ℤ) (2 : ℤ) := by
  exact noPrimitiveCoverResidue_of_square_check_mod4
    (d0 := (6 : ℤ)) (d1 := (3 : ℤ)) (d3 := (2 : ℤ)) (by native_decide)

/-- `(6,6,1)`, killed modulo `4`. -/
theorem noPrimitiveCoverResidue_6_6_1_mod4 :
    noPrimitiveCoverResidue 2 4 (6 : ℤ) (6 : ℤ) (1 : ℤ) := by
  exact noPrimitiveCoverResidue_of_square_check_mod4
    (d0 := (6 : ℤ)) (d1 := (6 : ℤ)) (d3 := (1 : ℤ)) (by native_decide)

/-- `(-1,-1,1)`, killed modulo `4`. -/
theorem noPrimitiveCoverResidue_neg1_neg1_1_mod4 :
    noPrimitiveCoverResidue 2 4 (-1 : ℤ) (-1 : ℤ) (1 : ℤ) := by
  exact noPrimitiveCoverResidue_of_square_check_mod4
    (d0 := (-1 : ℤ)) (d1 := (-1 : ℤ)) (d3 := (1 : ℤ)) (by native_decide)

/-- `(-1,-3,3)`, killed modulo `4`. -/
theorem noPrimitiveCoverResidue_neg1_neg3_3_mod4 :
    noPrimitiveCoverResidue 2 4 (-1 : ℤ) (-3 : ℤ) (3 : ℤ) := by
  exact noPrimitiveCoverResidue_of_square_check_mod4
    (d0 := (-1 : ℤ)) (d1 := (-3 : ℤ)) (d3 := (3 : ℤ)) (by native_decide)

/-- `(-1,-6,6)`, killed modulo `8`. -/
theorem noPrimitiveCoverResidue_neg1_neg6_6_mod8 :
    noPrimitiveCoverResidue 2 8 (-1 : ℤ) (-6 : ℤ) (6 : ℤ) := by
  exact noPrimitiveCoverResidue_of_square_check_mod8
    (d0 := (-1 : ℤ)) (d1 := (-6 : ℤ)) (d3 := (6 : ℤ)) (by native_decide)

/-- `(-2,-1,2)`, killed modulo `4`. -/
theorem noPrimitiveCoverResidue_neg2_neg1_2_mod4 :
    noPrimitiveCoverResidue 2 4 (-2 : ℤ) (-1 : ℤ) (2 : ℤ) := by
  exact noPrimitiveCoverResidue_of_square_check_mod4
    (d0 := (-2 : ℤ)) (d1 := (-1 : ℤ)) (d3 := (2 : ℤ)) (by native_decide)

/-- `(-2,-2,1)`, killed modulo `4`. -/
theorem noPrimitiveCoverResidue_neg2_neg2_1_mod4 :
    noPrimitiveCoverResidue 2 4 (-2 : ℤ) (-2 : ℤ) (1 : ℤ) := by
  exact noPrimitiveCoverResidue_of_square_check_mod4
    (d0 := (-2 : ℤ)) (d1 := (-2 : ℤ)) (d3 := (1 : ℤ)) (by native_decide)

/-- `(-2,-3,6)`, killed modulo `4`. -/
theorem noPrimitiveCoverResidue_neg2_neg3_6_mod4 :
    noPrimitiveCoverResidue 2 4 (-2 : ℤ) (-3 : ℤ) (6 : ℤ) := by
  exact noPrimitiveCoverResidue_of_square_check_mod4
    (d0 := (-2 : ℤ)) (d1 := (-3 : ℤ)) (d3 := (6 : ℤ)) (by native_decide)

/-- `(-2,-6,3)`, killed modulo `4`. -/
theorem noPrimitiveCoverResidue_neg2_neg6_3_mod4 :
    noPrimitiveCoverResidue 2 4 (-2 : ℤ) (-6 : ℤ) (3 : ℤ) := by
  exact noPrimitiveCoverResidue_of_square_check_mod4
    (d0 := (-2 : ℤ)) (d1 := (-6 : ℤ)) (d3 := (3 : ℤ)) (by native_decide)

/-- `(-3,-2,6)`, killed modulo `8`. -/
theorem noPrimitiveCoverResidue_neg3_neg2_6_mod8 :
    noPrimitiveCoverResidue 2 8 (-3 : ℤ) (-2 : ℤ) (6 : ℤ) := by
  exact noPrimitiveCoverResidue_of_square_check_mod8
    (d0 := (-3 : ℤ)) (d1 := (-2 : ℤ)) (d3 := (6 : ℤ)) (by native_decide)

/-- `(-3,-3,1)`, killed modulo `16`. -/
theorem noPrimitiveCoverResidue_neg3_neg3_1_mod16 :
    noPrimitiveCoverResidue 2 16 (-3 : ℤ) (-3 : ℤ) (1 : ℤ) := by
  exact noPrimitiveCoverResidue_of_square_check_mod16
    (d0 := (-3 : ℤ)) (d1 := (-3 : ℤ)) (d3 := (1 : ℤ)) (by native_decide)

/-- `(-3,-6,2)`, killed modulo `8`. -/
theorem noPrimitiveCoverResidue_neg3_neg6_2_mod8 :
    noPrimitiveCoverResidue 2 8 (-3 : ℤ) (-6 : ℤ) (2 : ℤ) := by
  exact noPrimitiveCoverResidue_of_square_check_mod8
    (d0 := (-3 : ℤ)) (d1 := (-6 : ℤ)) (d3 := (2 : ℤ)) (by native_decide)

/-- `(-6,-1,6)`, killed modulo `4`. -/
theorem noPrimitiveCoverResidue_neg6_neg1_6_mod4 :
    noPrimitiveCoverResidue 2 4 (-6 : ℤ) (-1 : ℤ) (6 : ℤ) := by
  exact noPrimitiveCoverResidue_of_square_check_mod4
    (d0 := (-6 : ℤ)) (d1 := (-1 : ℤ)) (d3 := (6 : ℤ)) (by native_decide)

/-- `(-6,-2,3)`, killed modulo `4`. -/
theorem noPrimitiveCoverResidue_neg6_neg2_3_mod4 :
    noPrimitiveCoverResidue 2 4 (-6 : ℤ) (-2 : ℤ) (3 : ℤ) := by
  exact noPrimitiveCoverResidue_of_square_check_mod4
    (d0 := (-6 : ℤ)) (d1 := (-2 : ℤ)) (d3 := (3 : ℤ)) (by native_decide)

/-- `(-6,-3,2)`, killed modulo `4`. -/
theorem noPrimitiveCoverResidue_neg6_neg3_2_mod4 :
    noPrimitiveCoverResidue 2 4 (-6 : ℤ) (-3 : ℤ) (2 : ℤ) := by
  exact noPrimitiveCoverResidue_of_square_check_mod4
    (d0 := (-6 : ℤ)) (d1 := (-3 : ℤ)) (d3 := (2 : ℤ)) (by native_decide)

/-- `(-6,-6,1)`, killed modulo `4`. -/
theorem noPrimitiveCoverResidue_neg6_neg6_1_mod4 :
    noPrimitiveCoverResidue 2 4 (-6 : ℤ) (-6 : ℤ) (1 : ℤ) := by
  exact noPrimitiveCoverResidue_of_square_check_mod4
    (d0 := (-6 : ℤ)) (d1 := (-6 : ℤ)) (d3 := (1 : ℤ)) (by native_decide)

end MazurProof.RationalPointsN12
```

## Brief performance notes

- The public `noPrimitiveCoverResidue_*` theorems prove the original variable-level obstruction, but the `native_decide` call is only on `noPrimitiveCoverResidueBySquares`.
- For `m = 16`, square residues are only `{0,1,4,9}`, so the fast check is essentially `4^4` square tuples rather than `16^4` variable tuples.
- The only semantic transfer needed is `squarePrimitiveTransfer_2_mod4/8/16`; these are tiny `native_decide` checks over one `Fin m` variable.
- The equations in `coverSquareResidue` use `Int` representatives and `% (m : ℤ)` to avoid heavier `ZMod` ring normalization. This is meant to stay computational and avoid `ring`/`field_simp` entirely in the certificates.
