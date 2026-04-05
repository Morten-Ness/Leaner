import Mathlib

variable {ι R S : Type*}

theorem IsAbsoluteValue.abv_sum [Semiring R] [Semiring S] [PartialOrder S] [IsOrderedRing S]
    (abv : R → S) [IsAbsoluteValue abv]
    (f : ι → R) (s : Finset ι) : abv (∑ i ∈ s, f i) ≤ ∑ i ∈ s, abv (f i) := (IsAbsoluteValue.toAbsoluteValue abv).sum_le _ _

nonrec lemma AbsoluteValue.map_prod [CommSemiring R] [Nontrivial R]
    [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
    (abv : AbsoluteValue R S) (f : ι → R) (s : Finset ι) :
    abv (∏ i ∈ s, f i) = ∏ i ∈ s, abv (f i) :=
  map_prod abv f s

