import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Nontrivial R]

variable [Semiring R]

theorem zero_notMem_multiset_map_X_add_C {α : Type*} (m : Multiset α) (f : α → R) :
    (0 : R[X]) ∉ m.map fun a => Polynomial.X + Polynomial.C (f a) := fun mem =>
  let ⟨_a, _, ha⟩ := Multiset.mem_map.mp mem
  Polynomial.X_add_C_ne_zero _ ha

