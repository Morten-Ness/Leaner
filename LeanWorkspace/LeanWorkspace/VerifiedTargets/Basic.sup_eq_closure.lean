import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem sup_eq_closure (N N' : Submonoid M) : N ⊔ N' = Submonoid.closure ((N : Set M) ∪ (N' : Set M)) := by
  simp_rw [Submonoid.closure_union, Submonoid.closure_eq]

