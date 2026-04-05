import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem δ_v (hnm : n + 1 = m) (z : CochainComplex.HomComplex.Cochain F G n) (p q : ℤ) (hpq : p + m = q) (q₁ q₂ : ℤ)
    (hq₁ : q₁ = q - 1) (hq₂ : p + 1 = q₂) : (CochainComplex.HomComplex.δ n m z).v p q hpq =
    z.v p q₁ (by rw [hq₁, ← hpq, ← hnm, ← add_assoc, add_sub_cancel_right]) ≫ G.d q₁ q
      + m.negOnePow • F.d p q₂ ≫ z.v q₂ q
          (by rw [← hq₂, add_assoc, add_comm 1, hnm, hpq]) := by
  obtain rfl : q₁ = p + n := by lia
  obtain rfl : q₂ = p + m - n := by lia
  rfl

