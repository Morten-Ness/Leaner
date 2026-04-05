import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable [DecidableEq ι]

theorem addHom_ext {γ : Type*} [AddZeroClass γ] ⦃f g : (⨁ i, β i) →+ γ⦄
    (H : ∀ (i : ι) (y : β i), f (DirectSum.of _ i y) = g (DirectSum.of _ i y)) : f = g := DFinsupp.addHom_ext H

