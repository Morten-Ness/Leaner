import Mathlib

variable {F α β γ : Type*}

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

variable [NonUnitalNonAssocSemiring γ]

theorem coe_comp_addMonoidHom (g : β →ₙ+* γ) (f : α →ₙ+* β) :
    AddMonoidHom.mk ⟨g ∘ f, (g.comp f).map_zero'⟩ (g.comp f).map_add' = (g : β →+ γ).comp f := rfl

