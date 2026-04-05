import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

set_option backward.isDefEq.respectTransparency false in
theorem shift_units_smul (a : ℤ) (x : Rˣ) :
    (x • γ).shift a = x • (γ.shift a) := by
  ext p q hpq
  dsimp
  simp only [CochainComplex.HomComplex.Cochain.shift_v', units_smul_v]

