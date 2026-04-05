import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A → B)

theorem supDegree_mem_range (hp : p ≠ 0) : p.supDegree D ∈ Set.range D := by
  obtain ⟨a, -, he⟩ := AddMonoidAlgebra.exists_supDegree_mem_support D hp; exact ⟨a, he.symm⟩

