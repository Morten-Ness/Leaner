import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A → B)

variable {ι : Type*} {s : Finset ι} {i : ι} (hi : i ∈ s) {f : ι → R[A]}

variable [AddZeroClass A]

theorem supDegree_add_eq_right (h : p.supDegree D < q.supDegree D) :
    (p + q).supDegree D = q.supDegree D := by
  rw [add_comm, AddMonoidAlgebra.supDegree_add_eq_left h]

