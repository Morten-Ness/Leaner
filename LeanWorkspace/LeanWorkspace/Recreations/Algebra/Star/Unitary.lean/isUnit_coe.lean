import Mathlib

variable {R : Type*}

variable [Monoid R] [StarMul R]

theorem isUnit_coe {U : unitary R} : IsUnit (U : R) := (Unitary.toUnits _).isUnit

