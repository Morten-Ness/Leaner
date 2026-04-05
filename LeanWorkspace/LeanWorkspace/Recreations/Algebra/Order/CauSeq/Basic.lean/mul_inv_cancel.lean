import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [DivisionRing β] {abv : β → α} [IsAbsoluteValue abv]

theorem mul_inv_cancel {f : CauSeq β abv} (hf) : f * CauSeq.inv f hf ≈ 1 := fun ε ε0 =>
  let ⟨K, K0, i, H⟩ := CauSeq.abv_pos_of_not_limZero hf
  ⟨i, fun j ij => by simpa [(abv_pos abv).1 (lt_of_lt_of_le K0 (H _ ij)), abv_zero abv] using ε0⟩

