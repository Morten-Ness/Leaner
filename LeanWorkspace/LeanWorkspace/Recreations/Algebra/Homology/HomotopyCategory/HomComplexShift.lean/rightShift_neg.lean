import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

theorem rightShift_neg (a n' : ℤ) (hn' : n' + a = n) :
    (-γ).rightShift a n' hn' = -γ.rightShift a n' hn' := by
  change CochainComplex.HomComplex.Cochain.rightShiftAddEquiv K L n a n' hn' (-γ) = _
  apply map_neg

