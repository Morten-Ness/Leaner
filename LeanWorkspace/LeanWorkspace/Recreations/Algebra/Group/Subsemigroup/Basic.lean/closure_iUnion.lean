import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem closure_iUnion {ι} (s : ι → Set M) : Subsemigroup.closure (⋃ i, s i) = ⨆ i, Subsemigroup.closure (s i) := (Subsemigroup.gi M).gc.l_iSup

