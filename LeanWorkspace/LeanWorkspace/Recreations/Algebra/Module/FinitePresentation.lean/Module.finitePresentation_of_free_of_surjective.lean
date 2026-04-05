import Mathlib

variable (R M N) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem Module.finitePresentation_of_free_of_surjective [Module.Free R M] [Module.Finite R M]
    (l : M →ₗ[R] N)
    (hl : Function.Surjective l) (hl' : (LinearMap.ker l).FG) :
    Module.FinitePresentation R N := by
  classical
  let b := Module.Free.chooseBasis R M
  let π : Free.ChooseBasisIndex R M → (Set.finite_range (l ∘ b)).toFinset :=
    fun i ↦ ⟨l (b i), by simp⟩
  have : π.Surjective := fun ⟨x, hx⟩ ↦ by
    obtain ⟨y, rfl⟩ : ∃ a, l (b a) = x := by simpa using hx
    exact ⟨y, rfl⟩
  choose σ hσ using this
  have hπ : Subtype.val ∘ π = l ∘ b := rfl
  have hσ₁ : π ∘ σ = id := by ext i; exact congr_arg Subtype.val (hσ i)
  have hσ₂ : l ∘ b ∘ σ = Subtype.val := by ext i; exact congr_arg Subtype.val (hσ i)
  refine ⟨(Set.finite_range (l ∘ b)).toFinset,
    by simpa [Set.range_comp, LinearMap.range_eq_top], ?_⟩
  let f : M →ₗ[R] (Set.finite_range (l ∘ b)).toFinset →₀ R :=
    Finsupp.lmapDomain _ _ π ∘ₗ b.repr.toLinearMap
  convert hl'.map f
  ext x; simp only [LinearMap.mem_ker, Submodule.mem_map]
  constructor
  · intro hx
    refine ⟨b.repr.symm (x.mapDomain σ), ?_, ?_⟩
    · simp [Finsupp.apply_linearCombination, hσ₂, hx]
    · simp only [f, LinearMap.comp_apply, b.repr.apply_symm_apply,
        LinearEquiv.coe_toLinearMap, Finsupp.lmapDomain_apply]
      rw [← Finsupp.mapDomain_comp, hσ₁, Finsupp.mapDomain_id]
  · rintro ⟨y, hy, rfl⟩
    simp [f, hπ, ← Finsupp.apply_linearCombination, hy]

-- Ideally this should be an instance but it makes mathlib much slower.

