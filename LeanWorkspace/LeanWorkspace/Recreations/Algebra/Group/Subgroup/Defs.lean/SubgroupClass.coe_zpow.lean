import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable {M S : Type*} [DivInvMonoid M] [SetLike S M] [hSM : SubgroupClass S M] {H K : S}

variable [SetLike S G] [SubgroupClass S G]

theorem coe_zpow (x : H) (n : ℤ) : ((x ^ n : H) : G) = (x : G) ^ n := rfl

