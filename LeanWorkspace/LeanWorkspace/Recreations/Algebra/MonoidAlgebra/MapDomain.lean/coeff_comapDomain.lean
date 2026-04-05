import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

theorem coeff_comapDomain (f : M → N) (hf) (x : R[N]) :
    (MonoidAlgebra.comapDomain f hf x).coeff = x.coeff.comapDomain f hf.injOn := by simp [MonoidAlgebra.comapDomain]

