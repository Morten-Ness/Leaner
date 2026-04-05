import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

theorem comapDomain_zero (f : M → N) (hf) : MonoidAlgebra.comapDomain f hf (0 : R[N]) = 0 := by simp [MonoidAlgebra.comapDomain]

