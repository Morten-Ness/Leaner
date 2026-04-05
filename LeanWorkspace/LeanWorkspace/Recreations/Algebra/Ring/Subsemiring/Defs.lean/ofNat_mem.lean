import Mathlib

variable {S R : Type*} [AddMonoidWithOne R] [SetLike S R] (s : S)

theorem ofNat_mem [AddSubmonoidWithOneClass S R] (s : S) (n : ℕ) [n.AtLeastTwo] :
    ofNat(n) ∈ s := by
  rw [← Nat.cast_ofNat]; exact natCast_mem s n

