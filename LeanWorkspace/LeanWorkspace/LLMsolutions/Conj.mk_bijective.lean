FAIL
import Mathlib

variable {α : Type u} {β : Type v}

variable [CommMonoid α]

theorem mk_bijective : Function.Bijective (@ConjClasses.mk α _) := by
  constructor
  · intro a b h
    simpa only [ConjClasses, QuotientGroup.leftRel_apply, div_eq_mul_inv, inv_mul_cancel_left]
      using h
  · intro x
    refine Quotient.inductionOn x ?_
    intro a
    exact ⟨a, rfl⟩
