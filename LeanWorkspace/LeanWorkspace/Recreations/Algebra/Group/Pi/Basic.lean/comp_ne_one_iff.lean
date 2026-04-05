import Mathlib

variable {I : Type u}

variable {α β γ : Type*}

variable {f : I → Type v₁} {g : I → Type v₂} {h : I → Type v₃}

variable (x y : ∀ i, f i) (i : I)

theorem comp_ne_one_iff [One β] [One γ] (f : α → β) {g : β → γ} (hg : Function.Injective g) (hg0 : g 1 = 1) :
    g ∘ f ≠ 1 ↔ f ≠ 1 := (Function.comp_eq_one_iff f hg hg0).ne

