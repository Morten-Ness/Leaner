import Mathlib

open scoped Kronecker

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v}

variable [CommRing R]

variable {S T : Type*} [CommRing S] [CommRing T]

variable (f : R →+* S)

variable {R m : Type*} [CommSemiring R] [Fintype m] [DecidableEq m]

theorem _root_.Matrix.IsUnit.kronecker {x : Matrix n n R} {y : Matrix m m R}
    (hx : IsUnit x) (hy : IsUnit y) : IsUnit (x ⊗ₖ y) := Matrix.GeneralLinearGroup.kronecker hx.unit hy.unit |>.isUnit

