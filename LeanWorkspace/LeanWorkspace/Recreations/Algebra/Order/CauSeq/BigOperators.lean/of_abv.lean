import Mathlib

variable {α β : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Ring β]
  {abv : β → α} [IsAbsoluteValue abv]
  {f g : ℕ → β} {a : ℕ → α}

theorem of_abv (hf : IsCauSeq abs fun m ↦ ∑ n ∈ range m, abv (f n)) :
    IsCauSeq abv fun m ↦ ∑ n ∈ range m, f n := IsCauSeq.of_abv_le hf 0 fun _ _ ↦ le_rfl

