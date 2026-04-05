import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem closure_empty : Subsemigroup.closure (∅ : Set M) = ⊥ := (Subsemigroup.gi M).gc.l_bot

