import Mathlib

variable {ι R S : Type*}

theorem AbsoluteValue.sum_le [Semiring R] [Semiring S] [PartialOrder S] [IsOrderedRing S]
    (abv : AbsoluteValue R S)
    (s : Finset ι) (f : ι → R) : abv (∑ i ∈ s, f i) ≤ ∑ i ∈ s, abv (f i) := Finset.le_sum_of_subadditive abv (map_zero _).le abv.add_le _ _

