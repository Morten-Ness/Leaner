import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

theorem leftShift_zero (a n' : ℤ) (hn' : n + a = n') :
    (0 : CochainComplex.HomComplex.Cochain K L n).leftShift a n' hn' = 0 := by
  change CochainComplex.HomComplex.Cochain.leftShiftAddEquiv K L n a n' hn' 0 = 0
  apply map_zero

