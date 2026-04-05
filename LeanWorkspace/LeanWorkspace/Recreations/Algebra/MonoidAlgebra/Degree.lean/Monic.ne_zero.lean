import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A → B)

theorem Monic.ne_zero [Nonempty A] [Nontrivial R] (hp : p.Monic D) : p ≠ 0 := fun h => by
  simp_rw [Monic, h, AddMonoidAlgebra.leadingCoeff_zero, zero_ne_one] at hp

