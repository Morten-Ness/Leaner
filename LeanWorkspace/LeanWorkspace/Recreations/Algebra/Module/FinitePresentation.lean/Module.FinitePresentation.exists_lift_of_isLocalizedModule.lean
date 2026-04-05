import Mathlib

variable {R M N N'} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

variable [AddCommGroup N'] [Module R N'] (S : Submonoid R) (f : N →ₗ[R] N') [IsLocalizedModule S f]

theorem Module.FinitePresentation.exists_lift_of_isLocalizedModule
    [h : Module.FinitePresentation R M] (g : M →ₗ[R] N') :
    ∃ (h : M →ₗ[R] N) (s : S), f ∘ₗ h = s • g := by
  obtain ⟨σ, hσ, τ, hτ⟩ := h
  let π := Finsupp.linearCombination R ((↑) : σ → M)
  have hπ : Function.Surjective π :=
    LinearMap.range_eq_top.mp
      (by rw [range_linearCombination, Subtype.range_val, ← hσ])
  classical
  choose s hs using IsLocalizedModule.surj S f
  let i : σ → N :=
    fun x ↦ (∏ j ∈ σ.erase x.1, (s (g j)).2) • (s (g x)).1
  let s₀ := ∏ j ∈ σ, (s (g j)).2
  have hi : f ∘ₗ Finsupp.linearCombination R i = (s₀ • g) ∘ₗ π := by
    ext j
    simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply,
      linearCombination_single, one_smul, LinearMap.map_smul_of_tower, ← hs, LinearMap.smul_apply,
      i, s₀, π]
    rw [← mul_smul, Finset.prod_erase_mul]
    exact j.prop
  have : ∀ x : τ, ∃ s : S, s • (Finsupp.linearCombination R i x) = 0 := by
    intro x
    convert_to ∃ s : S, s • (Finsupp.linearCombination R i x) = s • 0
    · simp only [smul_zero]
    apply IsLocalizedModule.exists_of_eq (S := S) (f := f)
    rw [← LinearMap.comp_apply, map_zero, hi, LinearMap.comp_apply]
    convert map_zero (s₀ • g)
    rw [← LinearMap.mem_ker, ← hτ]
    exact Submodule.subset_span x.prop
  choose s' hs' using this
  let s₁ := ∏ i : τ, s' i
  have : LinearMap.ker π ≤ LinearMap.ker (s₁ • Finsupp.linearCombination R i) := by
    rw [← hτ, Submodule.span_le]
    intro x hxσ
    simp only [s₁]
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.smul_apply,
      ← Finset.prod_erase_mul _ _ (Finset.mem_univ ⟨x, hxσ⟩), mul_smul]
    convert smul_zero _
    exact hs' ⟨x, hxσ⟩
  refine ⟨Submodule.liftQ _ _ this ∘ₗ
    (LinearMap.quotKerEquivOfSurjective _ hπ).symm.toLinearMap, s₁ * s₀, ?_⟩
  ext x
  obtain ⟨x, rfl⟩ := hπ x
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, mul_smul, LinearMap.smul_comp, ← hi,
    ← LinearMap.comp_smul, LinearMap.comp_assoc, LinearMap.comp_assoc]
  simp

