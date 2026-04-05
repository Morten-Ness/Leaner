import Mathlib

variable (R M N) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

variable {ι} [Finite ι]

theorem Module.finitePresentation_of_surjective [h : Module.FinitePresentation R M] (l : M →ₗ[R] N)
    (hl : Function.Surjective l) (hl' : (LinearMap.ker l).FG) :
    Module.FinitePresentation R N := by
  classical
  obtain ⟨s, hs, hs'⟩ := h
  obtain ⟨t, ht⟩ := hl'
  have H : Function.Surjective (Finsupp.linearCombination R ((↑) : s → M)) :=
    LinearMap.range_eq_top.mp
      (by rw [range_linearCombination, Subtype.range_val, ← hs])
  apply Module.finitePresentation_of_free_of_surjective (l ∘ₗ linearCombination R Subtype.val)
    (hl.comp H)
  choose σ hσ using (show _ from H)
  have : Finsupp.linearCombination R Subtype.val '' (σ '' t) = t := by
    simp only [Set.image_image, hσ, Set.image_id']
  rw [LinearMap.ker_comp, ← ht, ← this, ← Submodule.map_span, Submodule.comap_map_eq,
    ← Finset.coe_image]
  exact Submodule.FG.sup ⟨_, rfl⟩ hs'

