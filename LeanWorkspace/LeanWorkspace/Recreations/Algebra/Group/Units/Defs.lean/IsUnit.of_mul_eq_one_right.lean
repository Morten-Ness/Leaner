import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

theorem IsUnit.of_mul_eq_one_right [Monoid M] [IsDedekindFiniteMonoid M] {b : M} (a : M)
    (h : a * b = 1) : IsUnit b := .of_mul_eq_one a <| mul_eq_one_symm h

