import Mathlib

variable {k G H : Type*}

variable {M α : Type*} [AddCommMonoid M] (f : SkewMonoidAlgebra M α) (a a' : α) (b : M)

theorem Function.update_self : f.update a (f.coeff a) = f := by
  rcases f with ⟨f⟩
  apply toFinsupp_injective
  simp

