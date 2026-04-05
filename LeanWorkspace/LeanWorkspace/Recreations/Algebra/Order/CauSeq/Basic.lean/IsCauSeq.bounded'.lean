import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Ring β]
  {abv : β → α} [IsAbsoluteValue abv] {f g : ℕ → β}

theorem bounded' (hf : IsCauSeq abv f) (x : α) : ∃ r > x, ∀ i, abv (f i) < r := let ⟨r, h⟩ := IsCauSeq.bounded hf
  ⟨max r (x + 1), (lt_add_one x).trans_le (le_max_right _ _),
    fun i ↦ (h i).trans_le (le_max_left _ _)⟩

