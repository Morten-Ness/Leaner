import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem Normal.subgroupOf {H : Subgroup G} (hH : H.Normal) (K : Subgroup G) :
    (H.subgroupOf K).Normal := hH.comap _

