import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem mem_closure_singleton {x y : M} : y ∈ closure ({x} : Set M) ↔ ∃ n : ℕ, x ^ n = y := by
  rw [Submonoid.closure_singleton_eq, mem_mrange]; rfl

