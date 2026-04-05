import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable {M S : Type*} [DivInvMonoid M] [SetLike S M] [hSM : SubgroupClass S M] {H K : S}

variable [SetLike S G] [SubgroupClass S G]

theorem subset_union [LE S] [IsConcreteLE S G] {H K L : S} :
    (H : Set G) ⊆ K ∪ L ↔ H ≤ K ∨ H ≤ L := by
  refine ⟨fun h ↦ ?_, fun h x xH ↦ h.imp (mem_of_le_of_mem · xH) (mem_of_le_of_mem · xH)⟩
  rw [or_iff_not_imp_left, SetLike.not_le_iff_exists, ← SetLike.coe_subset_coe]
  exact fun ⟨x, xH, xK⟩ y yH ↦ (h <| mul_mem xH yH).elim
    ((h yH).resolve_left fun yK ↦ xK <| (mul_mem_cancel_right yK).mp ·)
    (mul_mem_cancel_left <| (h xH).resolve_left xK).mp

