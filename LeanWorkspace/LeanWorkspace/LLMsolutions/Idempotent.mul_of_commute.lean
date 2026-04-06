import Mathlib

variable {M N S : Type*}

variable [Semigroup S] {a b : S}

theorem mul_of_commute (hab : Commute a b) (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) :
    IsIdempotentElem (a * b) := by
  dsimp [IsIdempotentElem] at ha hb ⊢
  calc
    (a * b) * (a * b) = a * (b * a) * b := by simp [mul_assoc]
    _ = a * (a * b) * b := by rw [hab.eq]
    _ = (a * a) * (b * b) := by simp [mul_assoc]
    _ = a * b := by rw [ha, hb]
