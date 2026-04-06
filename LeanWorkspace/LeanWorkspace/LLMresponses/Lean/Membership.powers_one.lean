import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem powers_one : Submonoid.powers (1 : M) = ⊥ := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨n, rfl⟩
    simp
  · intro hx
    simp at hx
    rw [hx]
    exact ⟨1, by simp⟩
