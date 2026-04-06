import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem mem_powers_iff (x z : M) : x ∈ Submonoid.powers z ↔ ∃ n : ℕ, z ^ n = x := by
  constructor
  · intro hx
    rcases hx with ⟨n, rfl⟩
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, rfl⟩
