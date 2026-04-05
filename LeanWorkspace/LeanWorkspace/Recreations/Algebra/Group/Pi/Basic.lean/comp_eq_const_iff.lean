import Mathlib

variable {I : Type u}

variable {α β γ : Type*}

variable {f : I → Type v₁} {g : I → Type v₂} {h : I → Type v₃}

variable (x y : ∀ i, f i) (i : I)

theorem comp_eq_const_iff (b : β) (f : α → β) {g : β → γ} (hg : Function.Injective g) :
    g ∘ f = Function.const _ (g b) ↔ f = Function.const _ b := hg.comp_left.eq_iff' rfl

