import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

set_option backward.isDefEq.respectTransparency false in
theorem leftShift_smul (a n' : ℤ) (hn' : n + a = n') (x : R) :
    (x • γ).leftShift a n' hn' = x • γ.leftShift a n' hn' := by
  ext p q hpq
  dsimp
  simp only [CochainComplex.HomComplex.Cochain.leftShift_v _ a n' hn' p q hpq (p + a) (by lia), smul_v, Linear.comp_smul,
    smul_comm x]

