import Mathlib

variable {R A B : Type*}

theorem commute_eps_right [Semiring R] (x : DualNumber R) : Commute x ε := (DualNumber.commute_eps_left x).symm

