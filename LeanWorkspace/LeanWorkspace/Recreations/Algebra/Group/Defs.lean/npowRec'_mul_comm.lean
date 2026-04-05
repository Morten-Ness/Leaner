import Mathlib

variable {G : Type*}

theorem npowRec'_mul_comm {M : Type*} [Semigroup M] [One M] {k : ℕ} (k0 : k ≠ 0) (m : M) :
    m * npowRec' k m = npowRec' k m * m := by
  induction k using Nat.strongRecOn with
  | ind k' ih =>
    match k' with
    | 1 => simp [npowRec']
    | k + 2 => simp [npowRec', ← mul_assoc, ih]

