import Mathlib

variable {R : Type*} [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R] [PosMulMono R]

variable {α : Type*}

variable [PosMulStrictMono R] [NeZero (1 : R)]

theorem prod_map_lt_prod_map {ι : Type*} {s : Multiset ι} (hs : s ≠ 0)
    (f : ι → R) (g : ι → R) (h0 : ∀ i ∈ s, 0 < f i) (h : ∀ i ∈ s, f i < g i) :
    (map f s).prod < (map g s).prod := by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, map_coe, prod_coe, ne_eq, coe_eq_zero] at *
  apply List.prod_map_lt_prod_map hs f g h0 h

