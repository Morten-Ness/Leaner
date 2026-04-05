import Mathlib

variable {α : Type u}

variable {M : Type*}

variable [Monoid M] {a b c : M}

theorem isUnit_iff_mulLeft_bijective {a : M} :
    IsUnit a ↔ Function.Bijective (a * ·) := ⟨fun h ↦ ⟨IsUnit.mul_right_injective h, fun y ↦ ⟨h.unit⁻¹ * y, by simp [← mul_assoc]⟩⟩, fun h ↦
    ⟨⟨a, _, (h.2 1).choose_spec, h.1
      (by simpa [mul_assoc] using congr_arg (· * a) (h.2 1).choose_spec)⟩, rfl⟩⟩

