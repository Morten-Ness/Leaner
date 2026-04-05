import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

theorem leftShift_neg (a n' : ℤ) (hn' : n + a = n') :
    (-γ).leftShift a n' hn' = -γ.leftShift a n' hn' := by
  change CochainComplex.HomComplex.Cochain.leftShiftAddEquiv K L n a n' hn' (-γ) = _
  apply map_neg

