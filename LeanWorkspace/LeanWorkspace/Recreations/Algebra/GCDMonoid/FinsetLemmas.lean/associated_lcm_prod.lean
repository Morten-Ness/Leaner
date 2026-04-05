import Mathlib

variable {ι α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem associated_lcm_prod {s : Finset ι} {f : ι → α} (h : Set.Pairwise s <| IsRelPrime.onFun f) :
    Associated (s.lcm f) (s.prod f) := associated_of_dvd_dvd (Finset.lcm_dvd_prod s f) (s.prod_dvd_of_isRelPrime h fun _ ↦ dvd_lcm)

