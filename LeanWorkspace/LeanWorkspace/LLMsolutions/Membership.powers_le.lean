import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem powers_le {n : M} {P : Submonoid M} : Submonoid.powers n ≤ P ↔ n ∈ P := by
  constructor
  · intro h
    exact h (show n ∈ Submonoid.powers n by exact ⟨1, by simp⟩)
  · intro hn
    intro x hx
    rcases hx with ⟨m, rfl⟩
    exact P.pow_mem hn m
