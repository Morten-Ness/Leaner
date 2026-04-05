import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

set_option backward.isDefEq.respectTransparency false in
theorem δ_rightShift (a n' m' : ℤ) (hn' : n' + a = n) (m : ℤ) (hm' : m' + a = m) :
    δ n' m' (γ.rightShift a n' hn') = a.negOnePow • (δ n m γ).rightShift a m' hm' := by
  by_cases hnm : n + 1 = m
  · have hnm' : n' + 1 = m' := by lia
    ext p q hpq
    dsimp
    rw [CochainComplex.HomComplex.Cochain.rightShift_v (δ n m γ) a m' hm' p q hpq _ rfl,
      δ_v n m hnm _ p (p + m) rfl (p + n) (p + 1) (by lia) rfl,
      δ_v n' m' hnm' _ p q hpq (p + n') (p + 1) (by lia) rfl,
      γ.rightShift_v a n' hn' p (p + n') rfl (p + n) rfl,
      γ.rightShift_v a n' hn' (p + 1) q _ (p + m) (by lia)]
    simp only [shiftFunctorObjXIso, shiftFunctor_obj_d',
      Linear.comp_units_smul, assoc, HomologicalComplex.XIsoOfEq_inv_comp_d,
      add_comp, HomologicalComplex.d_comp_XIsoOfEq_inv, Linear.units_smul_comp, smul_add,
      add_right_inj, smul_smul]
    simp only [← hm', add_comm m', Int.negOnePow_add, ← mul_assoc,
      Int.units_mul_self, one_mul]
  · have hnm' : ¬ n' + 1 = m' := fun _ => hnm (by lia)
    rw [δ_shape _ _ hnm', δ_shape _ _ hnm, CochainComplex.HomComplex.Cochain.rightShift_zero, smul_zero]

