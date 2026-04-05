import Mathlib

variable {R K : Type*}

theorem Even.all [Semiring R] [Invertible (2 : R)] (a : R) : Even a := .of_isUnit_two (isUnit_of_invertible _) _

