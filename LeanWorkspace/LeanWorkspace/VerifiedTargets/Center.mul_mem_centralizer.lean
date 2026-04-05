import Mathlib

variable {M : Type*} {S T : Set M}

variable [Semigroup M] {a b : M}

theorem mul_mem_centralizer (ha : a ∈ Set.centralizer S) (hb : b ∈ Set.centralizer S) :
    a * b ∈ Set.centralizer S := fun g hg ↦ by
  rw [mul_assoc, ← hb g hg, ← mul_assoc, ha g hg, mul_assoc]

