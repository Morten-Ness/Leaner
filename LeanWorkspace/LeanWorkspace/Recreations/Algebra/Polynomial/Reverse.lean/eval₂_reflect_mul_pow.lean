import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

variable {S : Type*} [CommSemiring S]

theorem eval₂_reflect_mul_pow (i : R →+* S) (x : S) [Invertible x] (N : ℕ) (f : R[X])
    (hf : f.natDegree ≤ N) : eval₂ i (⅟x) (Polynomial.reflect N f) * x ^ N = eval₂ i x f := by
  refine
    induction_with_natDegree_le (fun f => eval₂ i (⅟x) (Polynomial.reflect N f) * x ^ N = eval₂ i x f) _ ?_ ?_
      ?_ f hf
  · simp
  · intro n r _ hnN
    simp only [Polynomial.revAt_le hnN, Polynomial.reflect_C_mul_X_pow, eval₂_X_pow, eval₂_C, eval₂_mul]
    conv in x ^ N => rw [← Nat.sub_add_cancel hnN]
    rw [pow_add, ← mul_assoc, mul_assoc (i r), ← mul_pow, invOf_mul_self, one_pow, mul_one]
  · intros
    simp [*, add_mul]

