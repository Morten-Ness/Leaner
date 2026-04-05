import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Ring β]
  {abv : β → α} [IsAbsoluteValue abv] {f g : ℕ → β}

theorem cauchy₃ (hf : IsCauSeq abv f) {ε : α} (ε0 : 0 < ε) :
    ∃ i, ∀ j ≥ i, ∀ k ≥ j, abv (f k - f j) < ε := let ⟨i, H⟩ := IsCauSeq.cauchy₂ hf ε0
  ⟨i, fun _ ij _ jk => H _ (le_trans ij jk) _ ij⟩

