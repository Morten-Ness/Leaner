import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

theorem leftShift_units_smul (a n' : ℤ) (hn' : n + a = n') (x : Rˣ) :
    (x • γ).leftShift a n' hn' = x • γ.leftShift a n' hn' := by
  apply CochainComplex.HomComplex.Cochain.leftShift_smul

