import Mathlib

section

variable {M : Type*}

variable [AddMonoid M]

theorem ofAdd_image_nsmul (n : ℕ) (s : Set M) :
    ofAdd '' (n • s) = (ofAdd '' s) ^ n := by
  induction n with
  | zero => simp; rfl
  | succ n IH => simp [succ_nsmul, pow_succ, IH]

end

section

variable {M : Type*}

variable [AddMonoid M]

theorem ofAdd_image_setAdd (s t : Set M) :
    ofAdd '' (s + t) = ofAdd '' s * ofAdd '' t := by
  rw [← Set.image2_add, Set.image_image2_distrib ofAdd_add, Set.image2_mul]

end

section

variable {M : Type*}

variable [AddMonoid M]

theorem toAdd_image_nsmul (n : ℕ) (s : Set (Multiplicative M)) :
    toAdd '' (s ^ n) = n • (toAdd '' s) := by
  induction n with
  | zero => simp; rfl
  | succ n IH => simp [succ_nsmul, pow_succ, IH]

end

section

variable {M : Type*}

variable [AddMonoid M]

theorem toAdd_image_setMul (s t : Set (Multiplicative M)) :
    toAdd '' (s * t) = (toAdd '' s) + (toAdd '' t) := by
  rw [← Set.image2_mul, Set.image_image2_distrib toAdd_mul, Set.image2_add]

end
