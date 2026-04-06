import Mathlib

variable {I : Type u}

variable {α β γ : Type*}

variable {f : I → Type v₁} {g : I → Type v₂} {h : I → Type v₃}

variable (x y : ∀ i, f i) (i : I)

theorem comp_ne_one_iff [One β] [One γ] (f : α → β) {g : β → γ} (hg : Function.Injective g) (hg0 : g 1 = 1) :
    g ∘ f ≠ 1 ↔ f ≠ 1 := by
  constructor
  · intro h h'
    apply h
    funext a
    change g (f a) = 1
    rw [h']
    exact hg0
  · intro h h'
    apply h
    funext a
    apply hg
    have h'' : (g ∘ f) a = 1 := by
      exact congrFun h' a
    simpa [Function.comp, hg0] using h''
