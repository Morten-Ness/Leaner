import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

set_option backward.isDefEq.respectTransparency false in
theorem leftShift_add (a n' : ℤ) (hn' : n + a = n') :
    (γ₁ + γ₂).leftShift a n' hn' = γ₁.leftShift a n' hn' + γ₂.leftShift a n' hn' := by
  ext p q hpq
  dsimp
  simp only [CochainComplex.HomComplex.Cochain.leftShift_v _ a n' hn' p q hpq (p + a) (by lia), add_v, comp_add, smul_add]

