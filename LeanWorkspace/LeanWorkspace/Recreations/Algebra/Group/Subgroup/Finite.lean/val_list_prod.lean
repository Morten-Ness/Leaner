import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem val_list_prod (l : List H) : (l.prod : G) = (l.map Subtype.val).prod := SubmonoidClass.coe_list_prod l

