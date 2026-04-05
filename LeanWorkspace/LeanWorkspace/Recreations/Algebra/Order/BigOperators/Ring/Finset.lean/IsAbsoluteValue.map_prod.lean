import Mathlib

variable {ι R S : Type*}

theorem IsAbsoluteValue.map_prod [CommSemiring R] [Nontrivial R]
    [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
    (abv : R → S) [IsAbsoluteValue abv] (f : ι → R) (s : Finset ι) :
    abv (∏ i ∈ s, f i) = ∏ i ∈ s, abv (f i) := (IsAbsoluteValue.toAbsoluteValue abv).map_prod _ _

