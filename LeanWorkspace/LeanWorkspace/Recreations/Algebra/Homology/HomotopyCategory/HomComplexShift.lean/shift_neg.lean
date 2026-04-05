import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

theorem shift_neg (a : ℤ) :
    (-γ).shift a = -γ.shift a := by
  change CochainComplex.HomComplex.Cochain.shiftAddHom K L n a (-γ) = _
  apply map_neg

