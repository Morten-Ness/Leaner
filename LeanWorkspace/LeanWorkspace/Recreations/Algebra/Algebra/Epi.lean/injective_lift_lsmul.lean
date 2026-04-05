import Mathlib

variable (R A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A] [Algebra.IsEpi R A]

variable (M : Type*) [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

theorem injective_lift_lsmul :
    Function.Injective (lift <| LinearMap.restrictScalars₁₂ R R (LinearMap.lsmul A M)) := by
  /- Morally the proof is to recognise that we can construct the map `A ⊗[R] M → M` as a
  composition of (`A`-linear) equivalences:
  ```
  A ⊗[R] M ≃  A ⊗[R] (A ⊗[A] M)
           ≃ (A ⊗[R] A) ⊗[A] M
           ≃ A ⊗[A] M
           ≃ M
  ```
  However the second equivalence above requires a version of heterogeneous tensor product
  associativity which is problematic in Mathlib because `TensorProduct.leftModule` prioritises the
  left factor in any tensor product. We therefore formalise a slightly lower level proof below. -/
  suffices ∀ (a : A) (m : M), 1 ⊗ₜ[R] (a • m) = a ⊗ₜ[R] m by
    let f : M →ₗ[R] A ⊗[R] M :=
      { toFun m := 1 ⊗ₜ m
        map_add' m n := tmul_add _ _ _
        map_smul' r m := tmul_smul _ _ _ }
    have aux : f ∘ₗ (lift <| LinearMap.restrictScalars₁₂ R R (LinearMap.lsmul A M)) = .id := by
      ext a m; simpa using this a m
    exact HasLeftInverse.injective ⟨f, fun x ↦ congr($aux x)⟩
  intro a m
  let f : A ⊗[R] A →ₗ[R] A ⊗[R] M := lift
    { toFun x :=
      { toFun y := x ⊗ₜ (y • m)
        map_add' := by simp [add_smul, tmul_add]
        map_smul' := by simp }
      map_add' := by intros; ext; simp [add_tmul]
      map_smul' := by intros; ext; simp [smul_tmul'] }
  simpa [f] using congr_arg f (Algebra.tmul_comm R 1 a)

