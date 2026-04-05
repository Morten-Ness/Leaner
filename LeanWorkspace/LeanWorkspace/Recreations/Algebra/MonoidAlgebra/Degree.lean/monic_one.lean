import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A → B)

theorem monic_one [AddZeroClass A] (hD : D.Injective) : (1 : R[A]).Monic D := by
  rw [Monic, one_def, AddMonoidAlgebra.leadingCoeff_single hD]

