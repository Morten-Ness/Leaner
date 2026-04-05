import Mathlib

variable {ι : Sort uι} {R M N P : Type*}

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]

variable [Module R M] [Module R N] [Module R P]

theorem map₂_span_span (f : M →ₗ[R] N →ₗ[R] P) (s : Set M) (t : Set N) :
    Submodule.map₂ f (span R s) (span R t) = span R (Set.image2 (fun m n => f m n) s t) := by
  apply le_antisymm
  · rw [Submodule.map₂_le]
    apply @span_induction R M _ _ _ s
    on_goal 1 =>
      intro a ha
      apply @span_induction R N _ _ _ t
      · intro b hb
        exact subset_span ⟨_, ‹_›, _, ‹_›, rfl⟩
    all_goals
      intros
      simp only [*, add_mem, smul_mem, zero_mem, map_zero, map_add,
        LinearMap.zero_apply, LinearMap.add_apply, LinearMap.smul_apply, map_smul]
  · rw [span_le, image2_subset_iff]
    intro a ha b hb
    exact Submodule.apply_mem_map₂ _ (subset_span ha) (subset_span hb)

