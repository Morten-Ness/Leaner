import Mathlib

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable [CommSemiring R] (f : ι → R[X]) (t : Multiset R[X])

theorem leadingCoeff_multiset_prod' (h : (t.map leadingCoeff).prod ≠ 0) :
    t.prod.leadingCoeff = (t.map leadingCoeff).prod := by
  induction t using Multiset.induction_on with | empty => simp | cons a t ih => ?_
  simp only [Multiset.map_cons, Multiset.prod_cons] at h ⊢
  rw [Polynomial.leadingCoeff_mul']
  · rw [ih]
    simp only [ne_eq]
    apply right_ne_zero_of_mul h
  · rw [ih]
    · exact h
    simp only [ne_eq]
    apply right_ne_zero_of_mul h

