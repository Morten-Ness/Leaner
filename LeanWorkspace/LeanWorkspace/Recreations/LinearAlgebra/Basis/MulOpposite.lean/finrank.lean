import Mathlib

variable {R H : Type*}

theorem finrank [DivisionRing R] [AddCommGroup H] [Module R H] :
    Module.finrank R Hᵐᵒᵖ = Module.finrank R H := by
  let b := Basis.ofVectorSpace R H
  rw [Module.finrank_eq_nat_card_basis b, Module.finrank_eq_nat_card_basis b.mulOpposite]

