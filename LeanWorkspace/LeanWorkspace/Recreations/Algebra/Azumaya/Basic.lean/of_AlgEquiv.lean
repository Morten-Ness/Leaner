import Mathlib

open scoped TensorProduct

variable (R A B : Type*) [CommSemiring R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

theorem of_AlgEquiv (e : A ≃ₐ[R] B) [IsAzumaya R A] : IsAzumaya R B := let _ : Module.Projective R B := .of_equiv e.toLinearEquiv
  let _ : FaithfulSMul R B := .of_injective e e.injective
  let _ : Module.Finite R B := .equiv e.toLinearEquiv
  ⟨Function.Bijective.of_comp_iff (AlgHom.mulLeftRight R B)
    (Algebra.TensorProduct.congr e e.op).bijective |>.1 <| by
    rw [← AlgEquiv.coe_algHom, ← AlgHom.coe_comp, IsAzumaya.mulLeftRight_comp_congr]
    simp [IsAzumaya.AlgHom.mulLeftRight_bij]⟩

