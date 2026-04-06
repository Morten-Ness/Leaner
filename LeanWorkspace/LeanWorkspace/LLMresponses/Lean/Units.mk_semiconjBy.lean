import Mathlib

open scoped Int

variable {M : Type*}

variable [Monoid M]

theorem mk_semiconjBy (u : Mˣ) (x : M) : SemiconjBy (↑u) x (u * x * ↑u⁻¹) := by
  dsimp [SemiconjBy]
  simp [mul_assoc]
