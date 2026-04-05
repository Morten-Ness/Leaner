import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable {M S : Type*} [DivInvMonoid M] [SetLike S M] [hSM : SubgroupClass S M] {H K : S}

variable [SetLike S G] [SubgroupClass S G]

theorem exists_inv_mem_iff_exists_mem {P : G → Prop} :
    (∃ x : G, x ∈ H ∧ P x⁻¹) ↔ ∃ x ∈ H, P x := by
  constructor <;>
    · rintro ⟨x, x_in, hx⟩
      exact ⟨x⁻¹, inv_mem x_in, by simp [hx]⟩

