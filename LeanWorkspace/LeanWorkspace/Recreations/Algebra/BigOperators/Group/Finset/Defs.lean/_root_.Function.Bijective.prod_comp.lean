import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [Fintype ι] [Fintype κ]

variable [CommMonoid M]

theorem _root_.Function.Bijective.prod_comp {e : ι → κ} (he : e.Bijective) (g : κ → M) :
    ∏ i, g (e i) = ∏ i, g i := Fintype.prod_bijective _ he _ _ fun _ ↦ rfl

