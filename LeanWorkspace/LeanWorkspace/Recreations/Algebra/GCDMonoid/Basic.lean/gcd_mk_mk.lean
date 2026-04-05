import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

variable [IsCancelMulZero α]

variable [CommMonoidWithZero α] [GCDMonoid α]

private theorem map_mk_unit_aux {f : Associates α →* α}
    (hinv : Function.RightInverse f Associates.mk) (a : α) :
    a * ↑(Classical.choose (associated_map_mk hinv a)) = f (Associates.mk a) := Classical.choose_spec (associated_map_mk hinv a)


theorem gcd_mk_mk {a b : α} : gcd (Associates.mk a) (Associates.mk b) = Associates.mk (gcd a b) := rfl

