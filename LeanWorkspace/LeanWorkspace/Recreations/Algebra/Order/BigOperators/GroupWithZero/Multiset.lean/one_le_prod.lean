import Mathlib

variable {R : Type*} [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R] [PosMulMono R]

theorem one_le_prod {s : Multiset R} (h : ∀ a ∈ s, 1 ≤ a) : 1 ≤ s.prod := by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, prod_coe] at *
  apply List.one_le_prod h

