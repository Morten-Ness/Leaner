import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Ring β]
  {abv : β → α} [IsAbsoluteValue abv] {f g : ℕ → β}

theorem const (x : β) : IsCauSeq abv fun _ ↦ x := fun ε ε0 ↦ ⟨0, fun j _ => by simpa [abv_zero] using ε0⟩

