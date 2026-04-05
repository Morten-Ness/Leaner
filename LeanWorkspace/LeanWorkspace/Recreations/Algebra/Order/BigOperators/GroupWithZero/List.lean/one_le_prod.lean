import Mathlib

variable {R : Type*} [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R] [PosMulMono R]

theorem one_le_prod {s : List R} (h : ∀ a ∈ s, 1 ≤ a) : 1 ≤ s.prod := by
  induction s with
  | nil => simp
  | cons head tail hind =>
    simp only [prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at h
    exact one_le_mul_of_one_le_of_one_le h.1 (hind h.2)

