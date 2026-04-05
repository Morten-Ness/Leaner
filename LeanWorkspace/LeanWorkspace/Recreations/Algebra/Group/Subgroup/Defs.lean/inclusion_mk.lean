import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable {M S : Type*} [DivInvMonoid M] [SetLike S M] [hSM : SubgroupClass S M] {H K : S}

variable [SetLike S G] [SubgroupClass S G]

theorem inclusion_mk [LE S] [IsConcreteLE S G] {h : H ≤ K} (x : G) (hx : x ∈ H) :
    SubgroupClass.inclusion h ⟨x, hx⟩ = ⟨x, mem_of_le_of_mem h hx⟩ := rfl

