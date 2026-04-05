import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [Fintype ι] [Fintype κ]

variable [CommMonoid M]

theorem _root_.Equiv.prod_comp (e : ι ≃ κ) (g : κ → M) : ∏ i, g (e i) = ∏ i, g i := Fintype.prod_equiv e _ _ fun _ ↦ rfl

