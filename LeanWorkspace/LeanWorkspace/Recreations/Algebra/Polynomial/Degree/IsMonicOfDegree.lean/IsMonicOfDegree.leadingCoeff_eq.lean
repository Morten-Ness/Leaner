import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem IsMonicOfDegree.leadingCoeff_eq {p : R[X]} {n : ℕ} (hp : IsMonicOfDegree p n) :
    p.leadingCoeff = 1 := Monic.def.mp hp.monic

