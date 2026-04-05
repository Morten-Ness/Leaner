import Mathlib

variable (R : Type*) [Semiring R] (p q : R[X]) {S : Type*} [AddCommMonoid S] [Pow S ℕ] [Module R S]
  (x : S)

theorem smeval_add : (p + q).smeval x = p.smeval x + q.smeval x := by
  simp only [Polynomial.smeval_eq_sum]
  refine sum_add_index p q (Polynomial.smul_pow x) (fun _ ↦ ?_) (fun _ _ _ ↦ ?_)
  · rw [Polynomial.smul_pow, zero_smul]
  · rw [Polynomial.smul_pow, Polynomial.smul_pow, Polynomial.smul_pow, add_smul]

