import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem mem_closure {x : M} : x ∈ Subsemigroup.closure s ↔ ∀ S : Subsemigroup M, s ⊆ S → x ∈ S := Subsemigroup.mem_sInf

