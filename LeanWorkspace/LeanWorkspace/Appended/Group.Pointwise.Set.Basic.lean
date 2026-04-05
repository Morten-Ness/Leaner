import Mathlib

section

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem exists_inv_mem {p : α → Prop} : (∃ x, x⁻¹ ∈ s ∧ p x) ↔ ∃ x ∈ s, p x⁻¹ := by
  rw [← (Equiv.inv _).exists_congr_right]
  simp

end

section

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem forall_inv_mem {p : α → Prop} : (∀ x, x⁻¹ ∈ s → p x) ↔ ∀ x ∈ s, p x⁻¹ := by
  rw [← (Equiv.inv _).forall_congr_right]
  simp

end

section

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem image_inv_of_apply_inv_eq {f g : α → β} (H : ∀ x ∈ s, f x⁻¹ = g x) :
    f '' (s⁻¹) = g '' s := by
  rw [← Set.image_inv_eq_inv, Set.image_image]; exact Set.image_congr H

end

section

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem inv_eq_self_iff_inv_subset : s⁻¹ = s ↔ s⁻¹ ⊆ s := ⟨le_of_eq, fun h => antisymm h <| Set.inv_subset.mp h⟩

end

section

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem inv_mem_inv : a⁻¹ ∈ s⁻¹ ↔ a ∈ s := by simp only [Set.mem_inv, inv_inv]

end

section

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem inv_subset : s⁻¹ ⊆ t ↔ s ⊆ t⁻¹ := by rw [← Set.inv_subset_inv, inv_inv]

end

section

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem inv_subset_inv : s⁻¹ ⊆ t⁻¹ ↔ s ⊆ t := (Equiv.inv α).surjective.preimage_subset_preimage_iff

end

section

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem nonempty_inv : s⁻¹.Nonempty ↔ s.Nonempty := inv_involutive.surjective.nonempty_preimage

end
