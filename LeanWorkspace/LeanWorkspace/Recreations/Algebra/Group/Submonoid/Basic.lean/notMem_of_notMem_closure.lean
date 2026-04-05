import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem notMem_of_notMem_closure {P : M} (hP : P ∉ Submonoid.closure s) : P ∉ s := fun h =>
  hP (Submonoid.subset_closure h)

