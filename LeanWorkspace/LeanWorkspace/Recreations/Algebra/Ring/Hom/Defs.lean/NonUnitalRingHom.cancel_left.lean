import Mathlib

variable {F α β γ : Type*}

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

variable [NonUnitalNonAssocSemiring γ]

theorem cancel_left {g : β →ₙ+* γ} {f₁ f₂ : α →ₙ+* β} (hg : Function.Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ := ⟨fun h => NonUnitalRingHom.ext fun x => hg <| by rw [← NonUnitalRingHom.comp_apply, h, NonUnitalRingHom.comp_apply], fun h => h ▸ rfl⟩

