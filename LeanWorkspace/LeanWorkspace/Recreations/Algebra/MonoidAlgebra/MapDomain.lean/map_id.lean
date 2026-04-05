import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

theorem map_id (x : R[M]) : MonoidAlgebra.map (.id R) x = x := by simp [MonoidAlgebra.map, coeff, ofCoeff]

