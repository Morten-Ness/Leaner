import Mathlib

open scoped ComplexConjugate

variable {ι G R : Type*} [AddGroup G]

variable [CommSemiring R] [StarRing R] {f g : G → R}

theorem sum_conjneg [Fintype G] (f : G → R) : ∑ a, conjneg f a = ∑ a, conj (f a) := Fintype.sum_equiv (Equiv.neg _) _ _ fun _ ↦ rfl

