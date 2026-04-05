import Mathlib

section

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [Zero β] [SMulZeroClass α β] {s : Finset α} {t : Finset β} {a : α}

theorem Nonempty.smul_zero (hs : s.Nonempty) : s • (0 : Finset β) = 0 := Finset.smul_zero_subset s.antisymm <| by simpa [mem_smul] using hs

end

section

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [Zero α] [Zero β] [SMulWithZero α β] {s : Finset α} {t : Finset β}

theorem Nonempty.zero_smul (ht : t.Nonempty) : (0 : Finset α) • t = 0 := Finset.zero_smul_subset t.antisymm <| by simpa [mem_smul] using ht

end

section

open scoped Pointwise RightActions

variable {α β : Type*} [DecidableEq β]

variable [GroupWithZero α]

variable [DecidableEq α] {s : Finset α}

theorem inv_op_smul_finset_distrib₀ (a : α) (s : Finset α) : (s <• a)⁻¹ = a⁻¹ • s⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  -- was `simp` and very slow (https://github.com/leanprover-community/mathlib4/issues/19751)
  · ext; simp only [mem_inv', ne_eq, MulOpposite.op_eq_zero_iff, not_false_eq_true, ←
      Finset.inv_smul_mem_iff₀, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_inv, MulOpposite.unop_op,
      inv_eq_zero, inv_inv, smul_eq_mul, mul_inv_rev, ha]

end

section

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [GroupWithZero α]

variable [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem inv_smul_mem_iff₀ (ha : a ≠ 0) : a⁻¹ • b ∈ s ↔ b ∈ a • s := show _ ↔ _ ∈ Units.mk0 a ha • _ from inv_smul_mem_iff

end

section

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [GroupWithZero α]

variable [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem mem_inv_smul_finset_iff₀ (ha : a ≠ 0) : b ∈ a⁻¹ • s ↔ a • b ∈ s := show _ ∈ (Units.mk0 a ha)⁻¹ • _ ↔ _ from mem_inv_smul_finset_iff

end

section

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [GroupWithZero α]

variable [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem smul_finset_inter₀ (ha : a ≠ 0) : a • (s ∩ t) = a • s ∩ a • t := image_inter _ _ <| MulAction.injective₀ ha

end

section

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [Monoid α] [AddGroup β] [DistribMulAction α β]

theorem smul_finset_neg (a : α) (t : Finset β) : a • -t = -(a • t) := by
  simp only [← image_smul, ← image_neg_eq_neg, Function.comp_def, image_image, smul_neg]

end

section

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [GroupWithZero α]

variable [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem smul_finset_sdiff₀ (ha : a ≠ 0) : a • (s \ t) = a • s \ a • t := image_sdiff _ _ <| MulAction.injective₀ ha

end

section

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [GroupWithZero α]

variable [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem smul_finset_subset_iff₀ (ha : a ≠ 0) : a • s ⊆ t ↔ s ⊆ a⁻¹ • t := show Units.mk0 a ha • _ ⊆ _ ↔ _ from smul_finset_subset_iff

end

section

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [GroupWithZero α]

variable [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem smul_finset_subset_smul_finset_iff₀ (ha : a ≠ 0) : a • s ⊆ a • t ↔ s ⊆ t := show Units.mk0 a ha • _ ⊆ _ ↔ _ from smul_finset_subset_smul_finset_iff

end

section

open scoped Pointwise symmDiff

variable {α β : Type*} [DecidableEq β]

variable [GroupWithZero α]

variable [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem smul_finset_symmDiff₀ (ha : a ≠ 0) : a • s ∆ t = (a • s) ∆ (a • t) := image_symmDiff _ _ <| MulAction.injective₀ ha

end

section

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [GroupWithZero α]

variable [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem smul_finset_univ₀ [Fintype β] (ha : a ≠ 0) : a • (univ : Finset β) = univ := coe_injective <| by push_cast; exact Set.smul_set_univ₀ ha

end

section

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [GroupWithZero α]

variable [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem smul_univ₀' [Fintype β] {s : Finset α} (hs : s.Nontrivial) : s • (univ : Finset β) = univ := coe_injective <| by push_cast; exact Set.smul_univ₀' hs

end

section

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [GroupWithZero α]

variable [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem smul_univ₀ [Fintype β] {s : Finset α} (hs : ¬s ⊆ 0) : s • (univ : Finset β) = univ := coe_injective <| by
    rw [← coe_subset] at hs
    push_cast at hs ⊢
    exact Set.smul_univ₀ hs

end

section

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [GroupWithZero α]

variable [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem subset_smul_finset_iff₀ (ha : a ≠ 0) : s ⊆ a • t ↔ a⁻¹ • s ⊆ t := show _ ⊆ Units.mk0 a ha • _ ↔ _ from subset_smul_finset_iff

end

section

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [Zero β] [SMulZeroClass α β] {s : Finset α} {t : Finset β} {a : α}

theorem zero_mem_smul_finset (h : (0 : β) ∈ t) : (0 : β) ∈ a • t := mem_smul_finset.2 ⟨0, h, smul_zero _⟩

end

section

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [Zero α] [Zero β] [SMulWithZero α β] {s : Finset α} {t : Finset β}

theorem zero_smul_finset_subset (s : Finset β) : (0 : α) • s ⊆ 0 := image_subset_iff.2 fun x _ ↦ mem_zero.2 <| zero_smul α x

end
