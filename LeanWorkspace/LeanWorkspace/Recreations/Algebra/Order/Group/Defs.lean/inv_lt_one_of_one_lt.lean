import Mathlib

variable {α : Type u}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {a b : α}

theorem inv_lt_one_of_one_lt : 1 < a → a⁻¹ < 1 := inv_lt_one_iff_one_lt.mpr

--  The additive version is also a `linarith` lemma.

