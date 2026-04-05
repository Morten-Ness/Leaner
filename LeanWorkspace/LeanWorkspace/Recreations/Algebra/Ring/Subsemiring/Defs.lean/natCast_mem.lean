import Mathlib

variable {S R : Type*} [AddMonoidWithOne R] [SetLike S R] (s : S)

theorem natCast_mem [AddSubmonoidWithOneClass S R] (n : ℕ) : (n : R) ∈ s := by
  induction n <;> simp [zero_mem, add_mem, one_mem, *]

