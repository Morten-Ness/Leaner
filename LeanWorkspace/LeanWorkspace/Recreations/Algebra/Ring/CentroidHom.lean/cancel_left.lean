import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocSemiring α]

theorem cancel_left {g f₁ f₂ : CentroidHom α} (hg : Function.Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ := ⟨fun h ↦ CentroidHom.ext fun a ↦ hg <| by rw [← CentroidHom.comp_apply, h, CentroidHom.comp_apply], congr_arg _⟩

