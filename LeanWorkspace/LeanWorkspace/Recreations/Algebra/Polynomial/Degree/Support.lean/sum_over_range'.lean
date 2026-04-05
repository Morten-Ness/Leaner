import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem sum_over_range' [AddCommMonoid S] (p : R[X]) {f : ℕ → R → S} (h : ∀ n, f n 0 = 0) (n : ℕ)
    (hn : p.natDegree < n) : p.sum f = ∑ a ∈ range n, f a (coeff p a) := by
  have := Polynomial.supp_subset_range hn
  simp only [Polynomial.sum, support, coeff] at this ⊢
  exact Finsupp.sum_of_support_subset _ this _ fun n _hn => h n

