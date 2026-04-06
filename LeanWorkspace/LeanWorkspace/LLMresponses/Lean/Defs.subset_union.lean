import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable {M S : Type*} [DivInvMonoid M] [SetLike S M] [hSM : SubgroupClass S M] {H K : S}

variable [SetLike S G] [SubgroupClass S G]

theorem subset_union [LE S] [IsConcreteLE S G] {H K L : S} :
    (H : Set G) ⊆ K ∪ L ↔ H ≤ K ∨ H ≤ L := by
  simpa [SetLike.coe_subset_coe, Set.subset_def] using SubgroupClass.subset_union (H := H) (K := K) (L := L)
