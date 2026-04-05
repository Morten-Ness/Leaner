import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {M S : Type*} [DivInvMonoid M] [SetLike S M] [hSM : SubgroupClass S M] {H K : S}

variable [SetLike S G] [SubgroupClass S G]

theorem div_mem_comm_iff {a b : G} : a / b ∈ H ↔ b / a ∈ H := inv_div b a ▸ inv_mem_iff

