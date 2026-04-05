import Mathlib

variable {R K : Type*}

theorem Odd.all [Ring R] [Invertible (2 : R)] (a : R) : Odd a := .of_isUnit_two (isUnit_of_invertible _) _

