import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

theorem rightUnshift_zero (a n' : ℤ) (hn' : n' + a = n) :
    (0 : CochainComplex.HomComplex.Cochain K (L⟦a⟧) n').rightUnshift n hn' = 0 := by
  change (CochainComplex.HomComplex.Cochain.rightShiftAddEquiv K L n a n' hn').symm 0 = 0
  apply map_zero

