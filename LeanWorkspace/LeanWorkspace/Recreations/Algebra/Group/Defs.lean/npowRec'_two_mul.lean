import Mathlib

variable {G : Type*}

theorem npowRec'_two_mul {M : Type*} [Semigroup M] [One M] (k : ℕ) (m : M) :
    npowRec' (2 * k) m = npowRec' k (m * m) := by
  induction k using Nat.strongRecOn with
  | ind k' ih =>
    match k' with
    | 0 => rfl
    | 1 => simp [npowRec']
    | k + 2 => simp [npowRec', ← mul_assoc, ← ih]

