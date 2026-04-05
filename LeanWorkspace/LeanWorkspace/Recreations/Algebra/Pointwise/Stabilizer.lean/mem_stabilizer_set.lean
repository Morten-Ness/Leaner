import Mathlib

open scoped Pointwise

variable {G H α : Type*}

variable [Group G] [Group H] [MulAction G α] {a : G} {s t : Set α}

theorem mem_stabilizer_set {s : Set α} : a ∈ stabilizer G s ↔ ∀ b, a • b ∈ s ↔ b ∈ s := by
  refine mem_stabilizer_iff.trans ⟨fun h b ↦ ?_, fun h ↦ ?_⟩
  · rw [← (smul_mem_smul_set_iff : a • b ∈ _ ↔ _), h]
  simp_rw [Set.ext_iff, mem_smul_set_iff_inv_smul_mem]
  exact ((MulAction.toPerm a).forall_congr' <| by simp [Iff.comm]).1 h

