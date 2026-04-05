import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable {M S : Type*} [DivInvMonoid M] [SetLike S M] [hSM : SubgroupClass S M] {H K : S}

variable [SetLike S G] [SubgroupClass S G]

theorem coe_inclusion [LE S] [IsConcreteLE S G]
    {H K : S} (h : H ≤ K) (a : H) : (SubgroupClass.inclusion h a : G) = a := Set.coe_inclusion (SetLike.coe_subset_coe.mpr h) a

