import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A → B)

variable {ι : Type*} {s : Finset ι} {i : ι} (hi : i ∈ s) {f : ι → R[A]}

variable [AddZeroClass A]

theorem leadingCoeff_ne_zero (hD : D.Injective) : p.leadingCoeff D ≠ 0 ↔ p ≠ 0 := (AddMonoidAlgebra.leadingCoeff_eq_zero hD).ne

