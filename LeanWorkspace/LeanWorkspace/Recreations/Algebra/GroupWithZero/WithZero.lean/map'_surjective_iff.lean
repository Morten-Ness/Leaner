import Mathlib

variable {α β γ : Type*}

variable [MulOneClass α]

variable [MulOneClass β] [MulOneClass γ]

theorem map'_surjective_iff {f : α →* β} : Function.Surjective (WithZero.map' f) ↔ Function.Surjective f := by
  simp only [Function.Surjective, «forall»]
  refine ⟨fun h b ↦ ?_, fun h ↦ ⟨⟨0, by simp⟩, fun b ↦ ?_⟩⟩
  · obtain ⟨a, hab⟩ := h.2 b
    induction a using WithZero.recZeroCoe <;>
    simp at hab
    grind
  · obtain ⟨a, ha⟩ := h b
    use a
    simp [ha]

alias ⟨_, map'_surjective⟩ := map'_surjective_iff

