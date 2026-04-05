import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [Fintype ι] [Fintype κ]

variable [CommMonoid M]

theorem prod_equiv (e : ι ≃ κ) (f : ι → M) (g : κ → M) (h : ∀ x, f x = g (e x)) :
    ∏ x, f x = ∏ x, g x := Fintype.prod_bijective _ e.bijective _ _ h

