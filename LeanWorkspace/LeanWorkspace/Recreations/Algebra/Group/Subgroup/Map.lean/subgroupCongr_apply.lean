import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

variable {H K : Subgroup G}

theorem subgroupCongr_apply (h : H = K) (x) :
    (MulEquiv.subgroupCongr h x : G) = x := rfl

