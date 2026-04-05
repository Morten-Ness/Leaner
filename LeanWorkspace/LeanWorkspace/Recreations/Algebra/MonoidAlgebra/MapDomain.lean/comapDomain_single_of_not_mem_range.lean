import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

theorem comapDomain_single_of_not_mem_range {r : R} {n : N} (hn : n ∉ Set.range f) (hf) :
    MonoidAlgebra.comapDomain f hf (single n r) = 0 := by simp [MonoidAlgebra.comapDomain, coeff, single, *]

