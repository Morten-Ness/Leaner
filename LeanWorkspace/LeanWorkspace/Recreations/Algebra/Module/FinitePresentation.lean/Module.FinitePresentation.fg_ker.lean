import Mathlib

variable (R M N) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

variable {ι} [Finite ι]

theorem Module.FinitePresentation.fg_ker [Module.Finite R M]
    [h : Module.FinitePresentation R N] (l : M →ₗ[R] N) (hl : Function.Surjective l) :
    (LinearMap.ker l).FG := by
  classical
  obtain ⟨s, hs, hs'⟩ := h
  have H : Function.Surjective (Finsupp.linearCombination R ((↑) : s → N)) :=
    LinearMap.range_eq_top.mp
      (by rw [range_linearCombination, Subtype.range_val, ← hs])
  obtain ⟨f, hf⟩ : ∃ f : (s →₀ R) →ₗ[R] M, l ∘ₗ f = (Finsupp.linearCombination R Subtype.val) := by
    choose f hf using show _ from hl
    exact ⟨Finsupp.linearCombination R (fun i ↦ f i), by ext; simp [hf]⟩
  have : (LinearMap.ker l).map (LinearMap.range f).mkQ = ⊤ := by
    rw [← top_le_iff]
    rintro x -
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    obtain ⟨y, hy⟩ := H (l x)
    rw [← hf, LinearMap.comp_apply, eq_comm, ← sub_eq_zero, ← map_sub] at hy
    exact ⟨_, hy, by simp⟩
  apply Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.range f).mkQ
  · rw [this]
    exact Module.Finite.fg_top
  · rw [Submodule.ker_mkQ, inf_comm, ← Submodule.map_comap_eq, ← LinearMap.ker_comp, hf]
    exact hs'.map f

