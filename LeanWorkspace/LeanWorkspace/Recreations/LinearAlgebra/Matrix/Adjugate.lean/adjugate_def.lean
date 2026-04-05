import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem adjugate_def (A : Matrix n n α) : Matrix.adjugate A = of fun i => Matrix.cramer Aᵀ (Pi.single i 1) := rfl

