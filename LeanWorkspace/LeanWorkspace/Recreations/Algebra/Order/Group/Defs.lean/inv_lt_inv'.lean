import Mathlib

variable {α : Type u}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {a b : α}

theorem inv_lt_inv' : a < b → b⁻¹ < a⁻¹ := inv_lt_inv_iff.mpr

--  The additive version is also a `linarith` lemma.

