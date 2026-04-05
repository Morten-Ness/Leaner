import Mathlib

variable {R : Type*} [Semiring R] [LinearOrder R] {a b : R} {m n : ℕ}

theorem add_le [IsStrictOrderedRing R] {α : Type*} [Add α] {f : α → R} (hf : ∀ x : α, 0 ≤ f x)
    (hna : IsNonarchimedean f) {a b : α} : f (a + b) ≤ f a + f b := by
  apply le_trans (hna _ _)
  rw [max_le_iff, le_add_iff_nonneg_right, le_add_iff_nonneg_left]
  exact ⟨hf _, hf _⟩

