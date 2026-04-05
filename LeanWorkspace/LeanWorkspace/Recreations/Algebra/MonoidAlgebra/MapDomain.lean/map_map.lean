import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

theorem map_map (f : S →+ T) (g : R →+ S) (x : R[M]) :
    MonoidAlgebra.map f (MonoidAlgebra.map g x) = MonoidAlgebra.map (f.comp g) x := by simp [MonoidAlgebra.map, coeff, ofCoeff]

