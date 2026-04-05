import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem notMem_of_notMem_closure {P : M} (hP : P ∉ Subsemigroup.closure s) : P ∉ s := fun h =>
  hP (Subsemigroup.subset_closure h)

