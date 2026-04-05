import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v}

variable [CommRing R]

theorem ext ⦃A B : GL n R⦄ (h : ∀ i j, (A : Matrix n n R) i j = (B : Matrix n n R) i j) : A = B := Units.ext <| Matrix.ext h

