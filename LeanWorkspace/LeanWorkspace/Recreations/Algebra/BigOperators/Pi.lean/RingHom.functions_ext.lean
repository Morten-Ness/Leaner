import Mathlib

open scoped Finset

variable {ι κ M N R α : Type*}

variable {I : Type*} [DecidableEq I] {R : I → Type*}

variable [∀ i, NonAssocSemiring (R i)]

theorem RingHom.functions_ext [Finite I] (S : Type*) [NonAssocSemiring S] (g h : (∀ i, R i) →+* S)
    (H : ∀ (i : I) (x : R i), g (single i x) = h (single i x)) : g = h := RingHom.coe_addMonoidHom_injective <|
    @AddMonoidHom.functions_ext I _ R _ _ S _ (g : (∀ i, R i) →+ S) h H

