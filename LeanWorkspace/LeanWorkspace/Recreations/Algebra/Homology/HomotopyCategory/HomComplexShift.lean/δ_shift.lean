import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

set_option backward.isDefEq.respectTransparency false in
theorem δ_shift (a m : ℤ) :
    δ n m (γ.shift a) = a.negOnePow • (δ n m γ).shift a := by
  by_cases hnm : n + 1 = m
  · ext p q hpq
    dsimp
    simp only [CochainComplex.HomComplex.Cochain.shift_v', shiftFunctor_obj_d',
      δ_v n m hnm _ p q hpq (q - 1) (p + 1) rfl rfl,
      δ_v n m hnm _ (p + a) (q + a) (by lia) (q - 1 + a) (p + 1 + a)
        (by lia) (by lia),
      smul_add, Linear.units_smul_comp, Linear.comp_units_smul, add_right_inj]
    rw [smul_comm]
  · rw [δ_shape _ _ hnm, δ_shape _ _ hnm, CochainComplex.HomComplex.Cochain.shift_zero, smul_zero]

