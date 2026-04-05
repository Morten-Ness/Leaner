import Mathlib

variable {ι M G S : Type*} [Monoid M] [CommGroup G] [LinearOrder S]

theorem IsMulIndecomposable.baseOf_subset_one_lt [Monoid S] (v : ι → M) (f : M →* S) :
    IsMulIndecomposable.baseOf v f ⊆ {i | 1 < f (v i)} := IsMulIndecomposable.subset _ _

