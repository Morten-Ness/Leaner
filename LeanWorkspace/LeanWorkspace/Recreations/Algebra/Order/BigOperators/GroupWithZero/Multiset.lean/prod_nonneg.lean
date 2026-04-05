import Mathlib

variable {R : Type*} [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R] [PosMulMono R]

theorem prod_nonneg {s : Multiset R} (h : ∀ a ∈ s, 0 ≤ a) : 0 ≤ s.prod := by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, prod_coe] at *
  apply List.prod_nonneg h

