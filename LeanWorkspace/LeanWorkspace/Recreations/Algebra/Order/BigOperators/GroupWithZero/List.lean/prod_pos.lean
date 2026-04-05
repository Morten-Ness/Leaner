import Mathlib

variable {R : Type*} [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R] [PosMulMono R]

variable [PosMulStrictMono R] [NeZero (1 : R)]

theorem prod_pos {s : List R} (h : ∀ a ∈ s, 0 < a) : 0 < s.prod := by
  induction s with
  | nil => simp
  | cons a s hind =>
    simp only [prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at h
    exact mul_pos h.1 (hind h.2)

