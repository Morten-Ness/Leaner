FAIL
import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem closure_eq_one_union (s : Set M) :
    Submonoid.closure s = {(1 : M)} ∪ (Subsemigroup.closure s : Set M) := by
  ext x
  constructor
  · intro hx
    by_cases h : x = 1
    · exact Or.inl h
    · right
      exact Subsemigroup.subset_closure hx h
  · rintro (rfl | hx)
    · exact Submonoid.one_mem _
    · exact Submonoid.closure_le.2 Subsemigroup.subset_closure hx
