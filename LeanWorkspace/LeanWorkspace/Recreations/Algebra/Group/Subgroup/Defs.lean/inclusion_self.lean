import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable {M S : Type*} [DivInvMonoid M] [SetLike S M] [hSM : SubgroupClass S M] {H K : S}

variable [SetLike S G] [SubgroupClass S G]

theorem inclusion_self [Preorder S] [IsConcreteLE S G] (x : H) : SubgroupClass.inclusion le_rfl x = x := by
  cases x
  rfl

