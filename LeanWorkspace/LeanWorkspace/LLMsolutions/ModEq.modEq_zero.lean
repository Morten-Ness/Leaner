import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem modEq_zero : a ≡ b [PMOD 0] ↔ a = b := by
  constructor
  · intro h
    rcases h with ⟨n, hn⟩
    simpa using hn
  · intro h
    subst h
    exact ⟨0, by simp⟩
