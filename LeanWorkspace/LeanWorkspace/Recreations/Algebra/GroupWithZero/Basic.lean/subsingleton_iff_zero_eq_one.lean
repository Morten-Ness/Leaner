import Mathlib

variable {M₀ G₀ : Type*}

variable [MulZeroOneClass M₀]

theorem subsingleton_iff_zero_eq_one : (0 : M₀) = 1 ↔ Subsingleton M₀ := ⟨fun h => haveI := uniqueOfZeroEqOne h; inferInstance, fun h => @Subsingleton.elim _ h _ _⟩

alias ⟨subsingleton_of_zero_eq_one, _⟩ := subsingleton_iff_zero_eq_one

