import Mathlib

section

variable {α : Type u}

variable {M : Type*}

variable [Monoid M] {a b c : M}

theorem isUnit_iff_mulLeft_bijective {a : M} :
    IsUnit a ↔ Function.Bijective (a * ·) := ⟨fun h ↦ ⟨IsUnit.mul_right_injective h, fun y ↦ ⟨h.unit⁻¹ * y, by simp [← mul_assoc]⟩⟩, fun h ↦
    ⟨⟨a, _, (h.2 1).choose_spec, h.1
      (by simpa [mul_assoc] using congr_arg (· * a) (h.2 1).choose_spec)⟩, rfl⟩⟩

end

section

variable {α : Type u}

variable {M : Type*}

variable [Monoid M] {a b c : M}

theorem isUnit_iff_mulRight_bijective {a : M} :
    IsUnit a ↔ Function.Bijective (· * a) := ⟨fun h ↦ ⟨IsUnit.mul_left_injective h, fun y ↦ ⟨y * h.unit⁻¹, by simp [mul_assoc]⟩⟩,
    fun h ↦ ⟨⟨a, _, h.1 (by simpa [mul_assoc] using congr_arg (a * ·) (h.2 1).choose_spec),
      (h.2 1).choose_spec⟩, rfl⟩⟩

end

section

variable {α : Type u}

variable [Monoid α]

variable (b c : αˣ) {u : αˣ}

theorem val_inv_inj {u₁ u₂ : αˣ} : ((u₁⁻¹ : αˣ) : α) = u₂⁻¹ ↔ (u₁ : α) = u₂ := Units.ext_iff.symm.trans <| inv_inj.trans Units.ext_iff

end
