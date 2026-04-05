import Mathlib

variable {α : Type u} [Mul α]

theorem induction_on {C : Magma.AssocQuotient α → Prop} (x : Magma.AssocQuotient α)
    (ih : ∀ x, C (Magma.AssocQuotient.of x)) : C x := Quot.induction_on x ih

