import Mathlib

variable {R : Type*} [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R] [PosMulMono R]

variable {α : Type*}

variable [PosMulStrictMono R] [NeZero (1 : R)]

theorem prod_pos {s : Multiset R} (h : ∀ a ∈ s, 0 < a) : 0 < s.prod := by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, prod_coe] at *
  apply List.prod_pos h

