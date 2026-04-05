import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

theorem comapDomain_single_map (f : M → N) (hf) (m : M) (r : R) :
    MonoidAlgebra.comapDomain f hf (single (f m) r) = single m r := by simp [MonoidAlgebra.comapDomain, single, coeff, ofCoeff]

