import Mathlib

open scoped Ring

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem charpoly_inv (A : Matrix n n R) (h : IsUnit A) :
    A⁻¹.charpoly = (-1) ^ Fintype.card n * Polynomial.C A.det⁻¹ʳ * A.charpolyRev := by
  simpa using Matrix.charpoly_inv (A := A) h
