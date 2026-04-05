import Mathlib

variable {ι α β M N G k R : Type*}

variable [Fintype ι] [CommMonoid M] [PartialOrder M] [IsOrderedCancelMonoid M] {f : ι → M}

theorem one_lt_prod_iff_of_one_le (hf : 1 ≤ f) : 1 < ∏ i, f i ↔ 1 < f := by
  obtain rfl | hf := hf.eq_or_lt <;> simp [*, Fintype.one_lt_prod]

