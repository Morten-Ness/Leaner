import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [Monoid M] [Monoid N] {s : Set M}

theorem IsUnit.mem_submonoid_iff {M : Type*} [Monoid M] (a : M) :
    a ∈ IsUnit.submonoid M ↔ IsUnit a := by
  change a ∈ setOf IsUnit ↔ IsUnit a
  rw [Set.mem_setOf_eq]

