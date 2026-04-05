import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

theorem leftShift_comp_zero_cochain (a n' : ℤ) (hn' : n + a = n') (γ' : CochainComplex.HomComplex.Cochain L M 0) :
    (γ.comp γ' (add_zero n)).leftShift a n' hn' =
      (γ.leftShift a n' hn').comp γ' (add_zero n') := by
  rw [CochainComplex.HomComplex.Cochain.leftShift_comp γ a n' hn' γ' (add_zero _) hn', mul_zero, Int.negOnePow_zero, one_smul]

