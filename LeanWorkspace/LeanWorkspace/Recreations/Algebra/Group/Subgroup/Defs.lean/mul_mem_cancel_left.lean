import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable {M S : Type*} [DivInvMonoid M] [SetLike S M] [hSM : SubgroupClass S M] {H K : S}

variable [SetLike S G] [SubgroupClass S G]

theorem mul_mem_cancel_left {x y : G} (h : x ∈ H) : x * y ∈ H ↔ y ∈ H := ⟨fun hab => by simpa using mul_mem (inv_mem h) hab, mul_mem h⟩

