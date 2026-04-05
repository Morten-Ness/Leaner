import Mathlib

section

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

end

section

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

theorem isEpi_iff_forall_one_tmul_eq :
    Algebra.IsEpi R A ↔ ∀ a : A, 1 ⊗ₜ[R] a = a ⊗ₜ[R] 1 := by
  refine ⟨fun h a ↦ IsEpi.injective_lift_mul <| by simp, fun h ↦ ⟨fun x y hxy ↦ ?_⟩⟩
  have h' (x : A ⊗[R] A) : ∃ a : A, x = a ⊗ₜ 1 := by
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul u v =>
      use u * v
      calc u ⊗ₜ[R] v = u ⊗ₜ[R] 1 * 1 ⊗ₜ[R] v := by simp
                   _ = u ⊗ₜ[R] 1 * v ⊗ₜ[R] 1 := by rw [h]
                   _ = (u * v) ⊗ₜ[R] 1 := by simp
    | add u v hu hv =>
      obtain ⟨u, rfl⟩ := hu
      obtain ⟨v, rfl⟩ := hv
      exact ⟨u  + v, by simp [add_tmul]⟩
  obtain ⟨a, rfl⟩ := h' x
  obtain ⟨b, rfl⟩ := h' y
  aesop

end

section

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

theorem isEpi_iff_surjective_algebraMap_of_finite [Module.Finite R A] :
    Algebra.IsEpi R A ↔ Function.Surjective (algebraMap R A) := by
  refine ⟨fun h ↦ ?_, Algebra.isEpi_of_surjective_algebraMap R A⟩
  let R' := (Algebra.linearMap R A).range
  rcases subsingleton_or_nontrivial (A ⧸ R') with h | _
  · rwa [Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top] at h
  have : Subsingleton ((A ⧸ R') ⊗[R] (A ⧸ R')) := by
    refine subsingleton_of_forall_eq 0 fun y ↦ ?_
    induction y with
    | zero => rfl
    | add a b e₁ e₂ => rwa [e₁, zero_add]
    | tmul x y =>
      obtain ⟨x, rfl⟩ := R'.mkQ_surjective x
      obtain ⟨y, rfl⟩ := R'.mkQ_surjective y
      obtain ⟨s, hs⟩ : ∃ s, 1 ⊗ₜ[R] s = x ⊗ₜ[R] y := by
        use x * y
        trans x ⊗ₜ 1 * 1 ⊗ₜ y
        · simp [(Algebra.isEpi_iff_forall_one_tmul_eq R A).mp]
        · simp
      have : R'.mkQ 1 = 0 := (Submodule.Quotient.mk_eq_zero R').mpr ⟨1, map_one (algebraMap R A)⟩
      rw [← map_tmul R'.mkQ R'.mkQ, ← hs, map_tmul, this, zero_tmul]
  cases false_of_nontrivial_of_subsingleton ((A ⧸ R') ⊗[R] (A ⧸ R'))

end

section

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

theorem isEpi_of_surjective_algebraMap (h : Function.Surjective (algebraMap R A)) :
    Algebra.IsEpi R A := by
  refine (Algebra.isEpi_iff_forall_one_tmul_eq R A).mpr fun a ↦ ?_
  obtain ⟨r, rfl⟩ := h a
  rw [algebraMap_eq_smul_one, smul_tmul]

end

section

variable (R A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A] [Algebra.IsEpi R A]

theorem tmul_comm (a b : A) :
    a ⊗ₜ[R] b = b ⊗ₜ[R] a := by
  have (a b : A) := calc a ⊗ₜ[R] b
      = a • (1 ⊗ₜ[R] b) := by rw [tmul_eq_smul_one_tmul]
    _ = a • (b ⊗ₜ[R] 1) := by rw [(Algebra.isEpi_iff_forall_one_tmul_eq R A).mp inferInstance b]
    _ = a • (b • (1 ⊗ₜ[R] 1)) := by rw [tmul_eq_smul_one_tmul]
  rw [this a b, this b a, smul_comm]

end
