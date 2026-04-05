import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable {M S : Type*} [DivInvMonoid M] [SetLike S M] [hSM : SubgroupClass S M] {H K : S}

variable [SetLike S G] [SubgroupClass S G]

theorem mul_mem_cancel_right {x y : G} (h : x ∈ H) : y * x ∈ H ↔ y ∈ H := ⟨fun hba => by simpa using mul_mem hba (inv_mem h), fun hb => mul_mem hb h⟩

