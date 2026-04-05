import Mathlib

variable {R : Type*} [Semiring R] {P : Type*} [AddCommMonoid P] [Module R P] {M : Type*}
  [AddCommMonoid M] [Module R M] {N : Type*} [AddCommMonoid N] [Module R N]

variable {Q : Type*} [AddCommMonoid Q] [Module R Q]

variable {ι : Type*} (A : ι → Type*) [∀ i : ι, AddCommMonoid (A i)] [∀ i : ι, Module R (A i)]

theorem Projective.of_equiv {R S} [Semiring R] [Semiring S] {M N}
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N]
    {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e₂ : M ≃ₛₗ[σ] N)
    [Projective R M] : Projective S N := by
  let e₁ : R ≃+* S := RingHomInvPair.toRingEquiv σ σ'
  obtain ⟨f, hf⟩ := ‹Projective R M›
  let g : N →ₗ[S] N →₀ S :=
  { toFun := fun x ↦ (equivCongrLeft e₂ (f (e₂.symm x))).mapRange e₁ e₁.map_zero
    map_add' := fun x y ↦ by ext; simp
    map_smul' := fun r v ↦ by ext i; simp [e₁, e₂.symm.map_smulₛₗ] }
  refine ⟨⟨g, fun x ↦ ?_⟩⟩
  replace hf := congr(e₂ $(hf (e₂.symm x)))
  simpa [linearCombination_apply, sum_mapRange_index, g, map_finsuppSum, e₂.map_smulₛₗ] using hf

