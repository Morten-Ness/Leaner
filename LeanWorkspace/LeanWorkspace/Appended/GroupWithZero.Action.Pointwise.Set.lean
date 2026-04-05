import Mathlib

section

open scoped Pointwise

variable {α β : Type*}

variable [Zero β] [SMulZeroClass α β] {s : Set α} {t : Set β} {a : α}

theorem Nonempty.smul_zero (hs : s.Nonempty) : s • (0 : Set β) = 0 := Set.smul_zero_subset s.antisymm <| by simpa [mem_smul] using hs

end

section

open scoped Pointwise

variable {α β : Type*}

variable [Zero α] [Zero β] [SMulWithZero α β] {s : Set α} {t : Set β}

theorem Nonempty.zero_smul (ht : t.Nonempty) : (0 : Set α) • t = 0 := Set.zero_smul_subset t.antisymm <| by simpa [mem_smul] using ht

end

section

open scoped Pointwise

variable {α β : Type*}

variable [GroupWithZero α] [MulAction α β] {s t : Set β} {a : α}

theorem mem_inv_smul_set_iff₀ (ha : a ≠ 0) (A : Set β) (x : β) : x ∈ a⁻¹ • A ↔ a • x ∈ A := show _ ∈ (Units.mk0 a ha)⁻¹ • _ ↔ _ from mem_inv_smul_set_iff

end

section

open scoped Pointwise

variable {α β : Type*}

variable [GroupWithZero α] [MulAction α β] {s t : Set β} {a : α}

theorem mem_smul_set_iff_inv_smul_mem₀ (ha : a ≠ 0) (A : Set β) (x : β) : x ∈ a • A ↔ a⁻¹ • x ∈ A := show _ ∈ Units.mk0 a ha • _ ↔ _ from mem_smul_set_iff_inv_smul_mem

end

section

open scoped Pointwise

variable {α β : Type*}

variable [GroupWithZero α] [MulAction α β] {s t : Set β} {a : α}

theorem smul_mem_smul_set_iff₀ (ha : a ≠ 0) (A : Set β) (x : β) : a • x ∈ a • A ↔ x ∈ A := show Units.mk0 a ha • _ ∈ _ ↔ _ from smul_mem_smul_set_iff

end

section

open scoped Pointwise

variable {α β : Type*}

variable [GroupWithZero α] [MulAction α β] {s t : Set β} {a : α}

theorem smul_set_inter₀ (ha : a ≠ 0) : a • (s ∩ t) = a • s ∩ a • t := show Units.mk0 a ha • _ = _ from smul_set_inter

end

section

open scoped Pointwise

variable {α β : Type*}

theorem smul_set_pi₀' {M ι : Type*} {α : ι → Type*} [GroupWithZero M] [∀ i, MulAction M (α i)]
    {c : M} {I : Set ι} (h : c ≠ 0 ∨ I = univ) (s : ∀ i, Set (α i)) : c • I.pi s = I.pi (c • s) := h.elim (fun hc ↦ smul_set_pi_of_isUnit (.mk0 _ hc) I s) (fun hI ↦ hI ▸ smul_set_univ_pi ..)

end

section

open scoped Pointwise

variable {α β : Type*}

theorem smul_set_pi₀ {M ι : Type*} {α : ι → Type*} [GroupWithZero M] [∀ i, MulAction M (α i)]
    {c : M} (hc : c ≠ 0) (I : Set ι) (s : ∀ i, Set (α i)) : c • I.pi s = I.pi (c • s) := smul_set_pi_of_isUnit (.mk0 _ hc) I s

end

section

open scoped Pointwise

variable {α β : Type*}

variable [GroupWithZero α] [MulAction α β] {s t : Set β} {a : α}

theorem smul_set_sdiff₀ (ha : a ≠ 0) : a • (s \ t) = a • s \ a • t := image_diff (MulAction.injective₀ ha) _ _

end

section

open scoped Pointwise

variable {α β : Type*}

variable [GroupWithZero α] [MulAction α β] {s t : Set β} {a : α}

theorem smul_set_subset_iff₀ (ha : a ≠ 0) {A B : Set β} : a • A ⊆ B ↔ A ⊆ a⁻¹ • B := show Units.mk0 a ha • _ ⊆ _ ↔ _ from smul_set_subset_iff_subset_inv_smul_set

end

section

open scoped Pointwise

variable {α β : Type*}

variable [GroupWithZero α] [MulAction α β] {s t : Set β} {a : α}

theorem smul_set_subset_smul_set_iff₀ (ha : a ≠ 0) {A B : Set β} : a • A ⊆ a • B ↔ A ⊆ B := show Units.mk0 a ha • _ ⊆ _ ↔ _ from smul_set_subset_smul_set_iff

end

section

open scoped Pointwise symmDiff

variable {α β : Type*}

variable [GroupWithZero α] [MulAction α β] {s t : Set β} {a : α}

theorem smul_set_symmDiff₀ (ha : a ≠ 0) : a • s ∆ t = (a • s) ∆ (a • t) := image_symmDiff (MulAction.injective₀ ha) _ _

end

section

open scoped Pointwise

variable {α β : Type*}

variable [GroupWithZero α] [MulAction α β] {s t : Set β} {a : α}

theorem smul_set_univ₀ (ha : a ≠ 0) : a • (univ : Set β) = univ := image_univ_of_surjective <| MulAction.surjective₀ ha

end

section

open scoped Pointwise

variable {α β : Type*}

variable [GroupWithZero α] [MulAction α β] {s t : Set β} {a : α}

theorem smul_univ₀' {s : Set α} (hs : s.Nontrivial) : s • (univ : Set β) = univ := Set.smul_univ₀ hs.not_subset_singleton

end

section

open scoped Pointwise

variable {α β : Type*}

variable [GroupWithZero α] [MulAction α β] {s t : Set β} {a : α}

theorem smul_univ₀ {s : Set α} (hs : ¬s ⊆ 0) : s • (univ : Set β) = univ := let ⟨a, ha, ha₀⟩ := not_subset.1 hs
  eq_univ_of_forall fun b ↦ ⟨a, ha, a⁻¹ • b, trivial, smul_inv_smul₀ ha₀ _⟩

end

section

open scoped Pointwise

variable {α β : Type*}

variable [GroupWithZero α] [MulAction α β] {s t : Set β} {a : α}

theorem subset_smul_set_iff₀ (ha : a ≠ 0) {A B : Set β} : A ⊆ a • B ↔ a⁻¹ • A ⊆ B := show _ ⊆ Units.mk0 a ha • _ ↔ _ from subset_smul_set_iff

end

section

open scoped Pointwise

variable {α β : Type*}

variable [Zero α] [Zero β] [SMulWithZero α β] {s : Set α} {t : Set β}

theorem subsingleton_zero_smul_set (s : Set β) : ((0 : α) • s).Subsingleton := subsingleton_singleton.anti <| Set.zero_smul_set_subset s

end

section

open scoped Pointwise

variable {α β : Type*}

variable [Zero α] [Zero β] [SMulWithZero α β] {s : Set α} {t : Set β}

theorem zero_smul_set_subset (s : Set β) : (0 : α) • s ⊆ 0 := image_subset_iff.2 fun x _ ↦ zero_smul α x

end
