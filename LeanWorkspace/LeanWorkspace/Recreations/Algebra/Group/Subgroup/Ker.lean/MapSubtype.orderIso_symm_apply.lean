import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem MapSubtype.orderIso_symm_apply (H : Subgroup G) (sH' : { H' : Subgroup G // H' ≤ H }) :
    (Subgroup.MapSubtype.orderIso H).symm sH' = sH'.1.subgroupOf H := rfl

