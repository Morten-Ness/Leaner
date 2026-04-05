import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable {M S : Type*} [DivInvMonoid M] [SetLike S M] [hSM : SubgroupClass S M] {H K : S}

variable [SetLike S G] [SubgroupClass S G]

theorem subtype_comp_inclusion [LE S] [IsConcreteLE S G]
    {H K : S} (h : H ≤ K) :
    (SubgroupClass.subtype K).comp (SubgroupClass.inclusion h) = SubgroupClass.subtype H := rfl

