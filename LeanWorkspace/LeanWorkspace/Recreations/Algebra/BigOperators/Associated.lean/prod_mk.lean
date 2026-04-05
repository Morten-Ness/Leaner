import Mathlib

variable {ι M M₀ : Type*}

variable [CommMonoid M]

theorem prod_mk {p : Multiset M} : (p.map Associates.mk).prod = Associates.mk p.prod := Multiset.induction_on p (by simp) fun a s ih => by simp [ih, Associates.mk_mul_mk]

