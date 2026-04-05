import Mathlib

open scoped TensorProduct

variable (R A B : Type*) [CommSemiring R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

theorem mulLeftRight_comp_congr (e : A ≃ₐ[R] B) :
    (AlgHom.mulLeftRight R B).comp (Algebra.TensorProduct.congr e e.op).toAlgHom =
    (e.toLinearEquiv.conjAlgEquiv R).toAlgHom.comp (AlgHom.mulLeftRight R A) := by
  ext <;> simp

