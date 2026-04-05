import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem adjugate_conjTranspose [StarRing α] (A : Matrix n n α) : A.adjugateᴴ = Matrix.adjugate Aᴴ := by
  dsimp only [conjTranspose]
  have : Aᵀ.adjugate.map star = Matrix.adjugate (Aᵀ.map star) := (starRingEnd α).map_adjugate Aᵀ
  rw [A.adjugate_transpose, this]

