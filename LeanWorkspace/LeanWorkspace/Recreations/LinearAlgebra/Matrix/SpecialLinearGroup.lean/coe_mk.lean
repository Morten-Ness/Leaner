import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

variable (A B : SpecialLinearGroup n R)

theorem coe_mk (A : Matrix n n R) (h : det A = 1) : ↑(⟨A, h⟩ : Matrix.SpecialLinearGroup n R) = A := rfl

