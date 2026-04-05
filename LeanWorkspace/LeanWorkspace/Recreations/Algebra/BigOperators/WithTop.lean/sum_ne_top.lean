import Mathlib

variable {ι M M₀ : Type*}

variable [AddCommMonoid M] {s : Finset ι} {f : ι → WithTop M}

theorem sum_ne_top : ∑ i ∈ s, f i ≠ ⊤ ↔ ∀ i ∈ s, f i ≠ ⊤ := by simp

