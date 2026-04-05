import Mathlib

variable {ι α β M N G k R : Type*}

variable [Fintype ι] [CommMonoid M] [PartialOrder M] [IsOrderedCancelMonoid M] {f : ι → M}

theorem prod_lt_one_iff_of_le_one (hf : f ≤ 1) : ∏ i, f i < 1 ↔ f < 1 := by
  obtain rfl | hf := hf.eq_or_lt <;> simp [*, Fintype.prod_lt_one]

