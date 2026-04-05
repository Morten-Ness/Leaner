import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem val_finset_prod {ι G} [CommGroup G] (H : Subgroup G) (f : ι → H) (s : Finset ι) :
    ↑(∏ i ∈ s, f i) = (∏ i ∈ s, f i : G) := SubmonoidClass.coe_finset_prod f s

