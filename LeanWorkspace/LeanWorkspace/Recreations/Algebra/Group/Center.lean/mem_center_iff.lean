import Mathlib

variable {M : Type*} {S T : Set M}

variable [Mul M]

theorem mem_center_iff {z : M} : z ∈ Set.center M ↔ IsMulCentral z := Iff.rfl

