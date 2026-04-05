import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

set_option backward.isDefEq.respectTransparency false in
theorem rightShift_smul (a n' : ℤ) (hn' : n' + a = n) (x : R) :
    (x • γ).rightShift a n' hn' = x • γ.rightShift a n' hn' := by
  ext p q hpq
  dsimp
  simp only [CochainComplex.HomComplex.Cochain.rightShift_v _ a n' hn' p q hpq _ rfl, smul_v, Linear.smul_comp]

