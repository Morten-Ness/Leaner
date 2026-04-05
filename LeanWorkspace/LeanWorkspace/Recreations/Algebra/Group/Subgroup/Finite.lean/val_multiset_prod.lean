import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem val_multiset_prod {G} [CommGroup G] (H : Subgroup G) (m : Multiset H) :
    (m.prod : G) = (m.map Subtype.val).prod := SubmonoidClass.coe_multiset_prod m

