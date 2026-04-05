import Mathlib

variable {F α β γ : Type*}

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

variable [NonUnitalNonAssocSemiring γ]

theorem cancel_right {g₁ g₂ : β →ₙ+* γ} {f : α →ₙ+* β} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ := ⟨fun h => NonUnitalRingHom.ext <| hf.forall.2 (NonUnitalRingHom.ext_iff.1 h), fun h => h ▸ rfl⟩

