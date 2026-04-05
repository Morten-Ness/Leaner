import Mathlib

variable {R : Type*} [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R] [PosMulMono R]

theorem prod_map_le_prod_map₀ {ι : Type*} {s : Multiset ι} (f : ι → R) (g : ι → R)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) :
    (map f s).prod ≤ (map g s).prod := by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, map_coe, prod_coe] at *
  apply List.prod_map_le_prod_map₀ f g h0 h

