import Mathlib

open scoped Matrix

variable {R : Type u} {n : Type w} [CommRing R] [DecidableEq n] [Fintype n]

variable (J : Matrix n n R)

theorem Matrix.lie_transpose (A B : Matrix n n R) : ⁅A, B⁆ᵀ = ⁅Bᵀ, Aᵀ⁆ := show (A * B - B * A)ᵀ = Bᵀ * Aᵀ - Aᵀ * Bᵀ by simp

