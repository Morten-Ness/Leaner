import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem coe_iInf {ι : Sort*} {S : ι → Subsemigroup M} : (↑(⨅ i, S i) : Set M) = ⋂ i, S i := by
  simp only [iInf, Subsemigroup.coe_sInf, Set.biInter_range]

