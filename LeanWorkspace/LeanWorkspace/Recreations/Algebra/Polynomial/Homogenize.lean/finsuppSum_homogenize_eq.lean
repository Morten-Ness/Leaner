import Mathlib

variable {R : Type*} [CommSemiring R]

theorem finsuppSum_homogenize_eq {M : Type*} [AddCommMonoid M] (p : R[X]) {f : R → M} :
    (Finsupp.sum (p.homogenize p.natDegree) fun _ c ↦ f c) = p.sum fun _ c ↦ f c := by
  rw [MvPolynomial.sum_def, sum_def p]
  -- We set up a bijection between the sets indexing the terms on both sides
  -- and show that it maps the terms in the one sum to those in the other.
  refine Finset.sum_nbij' (fun s ↦ s 0) (fun n ↦ fun₀ | 0 => n | 1 => p.natDegree - n)
    (fun s hs ↦ ?_) (fun n hn ↦ ?_) (fun s hs ↦ ?_) (fun n hn ↦ by simp)
    fun s hs ↦ ?_
  · simpa [Polynomial.coeff_homogenize, Polynomial.sum_eq_natDegree_of_mem_support_homogenize p hs] using hs
  · simpa [Polynomial.coeff_homogenize, mem_support_iff.mp hn]
      using Nat.add_sub_of_le <| le_natDegree_of_mem_supp n hn
  · -- speeds up `grind` quite a bit
    grind only [= Finsupp.update_apply, = Finsupp.single_apply,
      Polynomial.sum_eq_natDegree_of_mem_support_homogenize p hs]
  · simp [Polynomial.coeff_homogenize, Polynomial.sum_eq_natDegree_of_mem_support_homogenize p hs]

