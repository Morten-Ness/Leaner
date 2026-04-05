import Mathlib

open scoped Polynomial

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable [CommSemiring R] (f : ι → R[X]) (t : Multiset R[X])

theorem coeff_prod_of_natDegree_le (f : ι → R[X]) (n : ℕ) (h : ∀ p ∈ s, natDegree (f p) ≤ n) :
    coeff (∏ i ∈ s, f i) (#s * n) = ∏ i ∈ s, coeff (f i) n := by
  obtain ⟨l, hl⟩ := s
  convert Polynomial.coeff_multiset_prod_of_natDegree_le (l.map f) n ?_
  · simp
  · simp
  · simpa using h

