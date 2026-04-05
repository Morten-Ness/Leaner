import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

set_option backward.isDefEq.respectTransparency false in
theorem δ_leftShift (a n' m' : ℤ) (hn' : n + a = n') (m : ℤ) (hm' : m + a = m') :
    δ n' m' (γ.leftShift a n' hn') = a.negOnePow • (δ n m γ).leftShift a m' hm' := by
  by_cases hnm : n + 1 = m
  · have hnm' : n' + 1 = m' := by lia
    ext p q hpq
    dsimp
    rw [CochainComplex.HomComplex.Cochain.leftShift_v (δ n m γ) a m' hm' p q hpq (p + a) (by lia),
      δ_v n m hnm _ (p + a) q (by lia) (p + n') (p + 1 + a) (by lia) (by lia),
      δ_v n' m' hnm' _ p q hpq (p + n') (p + 1) (by lia) rfl,
      γ.leftShift_v a n' hn' p (p + n') rfl (p + a) (by lia),
      γ.leftShift_v a n' hn' (p + 1) q (by lia) (p + 1 + a) (by lia)]
    simp only [shiftFunctor_obj_X, shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_hom, id_comp, Linear.units_smul_comp, shiftFunctor_obj_d',
      Linear.comp_units_smul, smul_add, smul_smul]
    congr 2
    · rw [← hnm', add_comm n', mul_add, mul_one]
      simp only [Int.negOnePow_add, ← mul_assoc, Int.units_mul_self, one_mul]
    · simp only [← Int.negOnePow_add, ← hn', ← hm', ← hnm]
      congr 1
      linarith
  · have hnm' : ¬ n' + 1 = m' := fun _ => hnm (by lia)
    rw [δ_shape _ _ hnm', δ_shape _ _ hnm, CochainComplex.HomComplex.Cochain.leftShift_zero, smul_zero]

