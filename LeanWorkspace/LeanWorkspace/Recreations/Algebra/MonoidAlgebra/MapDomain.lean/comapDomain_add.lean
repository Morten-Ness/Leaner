import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

theorem comapDomain_add (f : M → N) (hf) (x y : R[N]) :
    MonoidAlgebra.comapDomain f hf (x + y) = MonoidAlgebra.comapDomain f hf x + MonoidAlgebra.comapDomain f hf y := by
  simp [MonoidAlgebra.comapDomain, comapDomain_add_of_injective hf]

