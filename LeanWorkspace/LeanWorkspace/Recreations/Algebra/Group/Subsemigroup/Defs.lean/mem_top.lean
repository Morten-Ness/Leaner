import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable {S : Subsemigroup M}

theorem mem_top (x : M) : x ∈ (⊤ : Subsemigroup M) := Set.mem_univ x

