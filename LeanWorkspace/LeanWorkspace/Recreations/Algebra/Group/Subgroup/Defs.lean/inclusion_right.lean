import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable {M S : Type*} [DivInvMonoid M] [SetLike S M] [hSM : SubgroupClass S M] {H K : S}

variable [SetLike S G] [SubgroupClass S G]

theorem inclusion_right [LE S] [IsConcreteLE S G] (h : H ≤ K) (x : K) (hx : (x : G) ∈ H) :
    SubgroupClass.inclusion h ⟨x, hx⟩ = x := by
  cases x
  rfl

