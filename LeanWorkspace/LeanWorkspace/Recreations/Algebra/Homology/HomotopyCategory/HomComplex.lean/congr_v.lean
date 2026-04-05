import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem congr_v {z₁ z₂ : CochainComplex.HomComplex.Cochain F G n} (h : z₁ = z₂) (p q : ℤ) (hpq : p + n = q) :
    z₁.v p q hpq = z₂.v p q hpq := by subst h; rfl

