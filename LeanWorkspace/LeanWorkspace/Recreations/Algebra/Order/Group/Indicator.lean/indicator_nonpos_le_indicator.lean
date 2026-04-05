import Mathlib

variable {ι : Sort*} {α M : Type*}

variable [Zero M] [LinearOrder M]

theorem indicator_nonpos_le_indicator (s : Set α) (f : α → M) :
    {a | f a ≤ 0}.indicator f ≤ s.indicator f := Set.indicator_le_indicator_nonneg (M := Mᵒᵈ) _ _

