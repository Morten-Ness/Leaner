import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable [Mul M]

theorem mul_apply_antidiagonal (x y : R[M]) (m : M) (s : Finset (M × M))
    (hs : ∀ {p}, p ∈ s ↔ p.1 * p.2 = m) : (x * y) m = ∑ p ∈ s, x p.1 * y p.2 := by
  classical
  let F (p : M × M) : R := if p.1 * p.2 = m then x p.1 * y p.2 else 0
  calc
    (x * y) m = ∑ m₁ ∈ x.support, ∑ m₂ ∈ y.support, F (m₁, m₂) := MonoidAlgebra.mul_apply ..
    _ = ∑ p ∈ x.support ×ˢ y.support with p.1 * p.2 = m, x p.1 * y p.2 := by
      rw [Finset.sum_filter, Finset.sum_product]
    _ = ∑ p ∈ s with p.1 ∈ x.support ∧ p.2 ∈ y.support, x p.1 * y p.2 := by
      congr! 1; MonoidAlgebra.ext; simp only [mem_filter, mem_product, hs, and_comm]
    _ = ∑ p ∈ s, x p.1 * y p.2 :=
      sum_subset (filter_subset _ _) fun p hps hp => by
        simp only [mem_filter, mem_support_iff, not_and, Classical.not_not] at hp ⊢
        by_cases h1 : x p.1 = 0
        · rw [h1, zero_mul]
        · rw [hp hps h1, mul_zero]

