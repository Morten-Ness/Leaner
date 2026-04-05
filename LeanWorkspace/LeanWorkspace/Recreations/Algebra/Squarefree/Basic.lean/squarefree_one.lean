import Mathlib

variable {R : Type*}

theorem squarefree_one [CommMonoid R] : Squarefree (1 : R) := isUnit_one.squarefree

