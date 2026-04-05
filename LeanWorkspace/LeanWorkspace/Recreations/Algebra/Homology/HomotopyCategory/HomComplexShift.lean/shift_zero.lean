import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

theorem shift_zero (a : ℤ) :
    (0 : CochainComplex.HomComplex.Cochain K L n).shift a = 0 := by
  change CochainComplex.HomComplex.Cochain.shiftAddHom K L n a 0 = 0
  apply map_zero

