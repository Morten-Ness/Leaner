import Mathlib

variable {M : Type*}

variable [AddMonoid M]

theorem toAdd_image_nsmul (n : ℕ) (s : Set (Multiplicative M)) :
    toAdd '' (s ^ n) = n • (toAdd '' s) := by
  induction n with
  | zero => simp; rfl
  | succ n IH => simp [succ_nsmul, pow_succ, IH]

