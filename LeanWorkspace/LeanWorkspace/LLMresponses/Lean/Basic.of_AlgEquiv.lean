FAIL
import Mathlib

open scoped TensorProduct

variable (R A B : Type*) [CommSemiring R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

theorem of_AlgEquiv (e : A ≃ₐ[R] B) [IsAzumaya R A] : IsAzumaya R B := by
  classical
  letI : Module.Free R B :=
    Module.Free.of_basis
      (Basis.ofEquivFun e.toLinearEquiv.symm (Module.Free.chooseBasis R A))
  letI : Module.Finite R B := by
    let hA : Module.Finite R A := inferInstance
    exact Module.Finite.of_surjective e.toLinearMap e.surjective
  letI : IsCentral R B := by
    letI : IsCentral R A := IsAzumaya.toIsCentral (R := R) (A := A)
    exact IsCentral.of_algEquiv e.symm
  exact ⟨inferInstance, inferInstance, inferInstance⟩
