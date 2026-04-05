import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [IsCancelMulZero α] [NormalizationMonoid α]

theorem out_mul (a b : Associates α) : (a * b).out = a.out * b.out := Quotient.inductionOn₂ a b fun _ _ => by
    simp only [Associates.quotient_mk_eq_mk, Associates.out_mk, mk_mul_mk, normalize.map_mul]

