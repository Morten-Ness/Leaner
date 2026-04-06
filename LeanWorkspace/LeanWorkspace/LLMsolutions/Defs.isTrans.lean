import Mathlib

variable {S M G : Type*}

variable [Semigroup S] {a b x y z x' y' : S}

theorem isTrans : IsTrans S fun a b ↦ ∃ c, SemiconjBy c a b :=
  by
    constructor
    intro a b c hab hbc
    rcases hab with ⟨d, hd⟩
    rcases hbc with ⟨e, he⟩
    refine ⟨e * d, ?_⟩
    dsimp [SemiconjBy] at hd he ⊢
    calc
      (e * d) * a = e * (d * a) := by simp [mul_assoc]
      _ = e * (b * d) := by rw [hd]
      _ = (e * b) * d := by simp [mul_assoc]
      _ = (c * e) * d := by rw [he]
      _ = c * (e * d) := by simp [mul_assoc]
