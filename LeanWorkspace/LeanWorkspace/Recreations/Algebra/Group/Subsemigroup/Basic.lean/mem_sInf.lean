import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem mem_sInf {S : Set (Subsemigroup M)} {x : M} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p := Set.mem_iInter₂

