import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

variable {_ : NonAssocSemiring γ}

theorem cancel_right {g₁ g₂ : β →+* γ} {f : α →+* β} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ := ⟨fun h => RingHom.ext <| hf.forall.2 (RingHom.ext_iff.1 h), fun h => h ▸ rfl⟩

