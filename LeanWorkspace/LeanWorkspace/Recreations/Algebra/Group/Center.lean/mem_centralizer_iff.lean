import Mathlib

variable {M : Type*} {S T : Set M}

variable [Mul M]

theorem mem_centralizer_iff {c : M} : c ∈ Set.centralizer S ↔ ∀ m ∈ S, m * c = c * m := Iff.rfl

