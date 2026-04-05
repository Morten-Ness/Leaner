import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable {S : Subsemigroup M}

theorem notMem_bot {x : M} : x ∉ (⊥ : Subsemigroup M) := Set.notMem_empty x

