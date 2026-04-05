import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

variable {_ : NonAssocSemiring γ}

theorem cancel_left {g : β →+* γ} {f₁ f₂ : α →+* β} (hg : Function.Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ := ⟨fun h => RingHom.ext fun x => hg <| by rw [← RingHom.comp_apply, h, RingHom.comp_apply], fun h => h ▸ rfl⟩

