import Mathlib

variable {M : Type*}

variable [AddMonoid M]

theorem ofAdd_image_nsmul (n : ℕ) (s : Set M) :
    ofAdd '' (n • s) = (ofAdd '' s) ^ n := by
  induction n with
  | zero => simp; rfl
  | succ n IH => simp [succ_nsmul, pow_succ, IH]

