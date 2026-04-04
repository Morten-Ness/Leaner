import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P]

theorem parallel_iff_direction_eq_and_eq_bot_iff_eq_bot {s₁ s₂ : AffineSubspace k P} :
    s₁ ∥ s₂ ↔ s₁.direction = s₂.direction ∧ (s₁ = ⊥ ↔ s₂ = ⊥) := by
  refine ⟨fun h => ⟨h.direction_eq, ?_, ?_⟩, fun h => ?_⟩
  · rintro rfl
    exact AffineSubspace.bot_parallel_iff_eq_bot.1 h
  · rintro rfl
    exact AffineSubspace.parallel_bot_iff_eq_bot.1 h
  · rcases h with ⟨hd, hb⟩
    by_cases hs₁ : s₁ = ⊥
    · rw [hs₁, AffineSubspace.bot_parallel_iff_eq_bot]
      exact hb.1 hs₁
    · have hs₂ : s₂ ≠ ⊥ := hb.not.1 hs₁
      rcases (nonempty_iff_ne_bot s₁).2 hs₁ with ⟨p₁, hp₁⟩
      rcases (nonempty_iff_ne_bot s₂).2 hs₂ with ⟨p₂, hp₂⟩
      refine ⟨p₂ -ᵥ p₁, (eq_iff_direction_eq_of_mem hp₂ ?_).2 ?_⟩
      · rw [AffineSubspace.mem_map]
        refine ⟨p₁, hp₁, ?_⟩
        simp
      · simpa using hd.symm

