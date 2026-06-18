import Mathlib

/-!
# A concrete model of `ℤ[φ]`, where `φ = (1 + √5) / 2`

Elements are represented as pairs `(a,b) : ℤ × ℤ`, interpreted as
`a + b φ`, with `φ^2 = φ + 1`.

The class-number-one/UFD step is deliberately isolated as an axiom:
if `α` and `conj α` are coprime and `α * conj α` is an integer square,
then `α` is a unit times a square.
-/

namespace Scratch.ChatGPTDropDM1

/-- The order `ℤ[φ]`, with `φ^2 = φ + 1`. -/
@[ext]
structure ZPhi where
  a : ℤ
  b : ℤ
deriving DecidableEq, Repr

namespace ZPhi

/-- The element `n + 0φ`. -/
def ofInt (n : ℤ) : ZPhi :=
  ⟨n, 0⟩

/-- Addition in the basis `1, φ`. -/
protected def add (x y : ZPhi) : ZPhi :=
  ⟨x.a + y.a, x.b + y.b⟩

/-- Negation in the basis `1, φ`. -/
protected def neg (x : ZPhi) : ZPhi :=
  ⟨-x.a, -x.b⟩

/-- Multiplication in the basis `1, φ`, using `φ^2 = φ + 1`. -/
protected def mul (x y : ZPhi) : ZPhi :=
  ⟨x.a * y.a + x.b * y.b,
    x.a * y.b + x.b * y.a + x.b * y.b⟩

instance : Zero ZPhi := ⟨ofInt 0⟩
instance : One ZPhi := ⟨ofInt 1⟩
instance : Add ZPhi := ⟨ZPhi.add⟩
instance : Neg ZPhi := ⟨ZPhi.neg⟩
instance : Sub ZPhi := ⟨fun x y => x + -y⟩
instance : Mul ZPhi := ⟨ZPhi.mul⟩

@[simp] theorem ofInt_a (n : ℤ) : (ofInt n).a = n := rfl
@[simp] theorem ofInt_b (n : ℤ) : (ofInt n).b = 0 := rfl

/-- Conjugation: `φ ↦ 1 - φ`.  Thus `a + bφ ↦ (a+b) - bφ`. -/
def conj (x : ZPhi) : ZPhi :=
  ⟨x.a + x.b, -x.b⟩

/-- The algebraic norm `N(a+bφ)=a²+ab-b²`. -/
def norm (x : ZPhi) : ℤ :=
  x.a ^ 2 + x.a * x.b - x.b ^ 2

/-- Square of an element, avoiding the need for a full ring instance. -/
def sq (x : ZPhi) : ZPhi :=
  x * x

/-- Divisibility in the multiplicative monoid of `ℤ[φ]`. -/
def Divides (d x : ZPhi) : Prop :=
  ∃ z : ZPhi, x = d * z

/-- Units in the concrete order. -/
def IsUnitZPhi (u : ZPhi) : Prop :=
  ∃ v : ZPhi, u * v = 1 ∧ v * u = 1

/-- Coprimality in `ℤ[φ]`: every common divisor is a unit. -/
def CoprimeZPhi (x y : ZPhi) : Prop :=
  ∀ d : ZPhi, Divides d x → Divides d y → IsUnitZPhi d

@[simp] theorem mul_a (x y : ZPhi) :
    (x * y).a = x.a * y.a + x.b * y.b := rfl

@[simp] theorem mul_b (x y : ZPhi) :
    (x * y).b = x.a * y.b + x.b * y.a + x.b * y.b := rfl

@[simp] theorem conj_a (x : ZPhi) : (conj x).a = x.a + x.b := rfl
@[simp] theorem conj_b (x : ZPhi) : (conj x).b = -x.b := rfl

/-- Conjugation is involutive. -/
theorem conj_conj (x : ZPhi) : conj (conj x) = x := by
  ext <;> simp [conj]

/-- Conjugation is multiplicative. -/
theorem conj_mul (x y : ZPhi) : conj (x * y) = conj x * conj y := by
  ext <;> simp [conj, ZPhi.mul] <;> ring

/-- `α * conj α` is the norm, embedded as an integer. -/
theorem mul_conj (x : ZPhi) : x * conj x = ofInt (norm x) := by
  ext <;> simp [conj, norm, ofInt, ZPhi.mul] <;> ring

/-- The norm is invariant under conjugation. -/
theorem norm_conj (x : ZPhi) : norm (conj x) = norm x := by
  simp [conj, norm]
  ring

/-- The norm is multiplicative. -/
theorem norm_mul (x y : ZPhi) : norm (x * y) = norm x * norm y := by
  simp [norm, ZPhi.mul]
  ring

/--
UFD/class-number-one square extraction axiom for `ℤ[φ]`.

Mathematically, this follows because `ℤ[(1+√5)/2]` is a UFD.  If `α` and
`conj α` are coprime and their product is an ordinary integer square, then
`α` is a unit times a square.
-/
axiom square_extraction_of_coprime_norm_square
    {α : ZPhi} {t : ℤ}
    (hsq : α * conj α = ofInt (t ^ 2))
    (hcop : CoprimeZPhi α (conj α)) :
    ∃ ε β : ZPhi, IsUnitZPhi ε ∧ α = ε * sq β

/-- The element `p² + q² φ`. -/
def alphaPQ (p q : ℤ) : ZPhi :=
  ⟨p ^ 2, q ^ 2⟩

/-- Norm of `p² + q² φ` is `p⁴ + p²q² - q⁴`. -/
theorem norm_alphaPQ (p q : ℤ) :
    norm (alphaPQ p q) = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4 := by
  simp [alphaPQ, norm]
  ring

/-- Product with the conjugate for `p² + q² φ`. -/
theorem alphaPQ_mul_conj (p q : ℤ) :
    alphaPQ p q * conj (alphaPQ p q) =
      ofInt (p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4) := by
  calc
    alphaPQ p q * conj (alphaPQ p q) = ofInt (norm (alphaPQ p q)) :=
      mul_conj (alphaPQ p q)
    _ = ofInt (p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4) := by
      rw [norm_alphaPQ]

/--
Application to the denominator quartic:
if `t² = p⁴+p²q²-q⁴` and `p²+q²φ` is coprime to its conjugate, then
`p²+q²φ` is a unit times a square in `ℤ[φ]`.
-/
theorem extract_square_for_alphaPQ
    (p q t : ℤ)
    (h : t ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4)
    (hcop : CoprimeZPhi (alphaPQ p q) (conj (alphaPQ p q))) :
    ∃ ε β : ZPhi, IsUnitZPhi ε ∧ alphaPQ p q = ε * sq β := by
  refine square_extraction_of_coprime_norm_square ?_ hcop
  calc
    alphaPQ p q * conj (alphaPQ p q) =
        ofInt (p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4) := alphaPQ_mul_conj p q
    _ = ofInt (t ^ 2) := by
      rw [← h]

end ZPhi

end Scratch.ChatGPTDropDM1
