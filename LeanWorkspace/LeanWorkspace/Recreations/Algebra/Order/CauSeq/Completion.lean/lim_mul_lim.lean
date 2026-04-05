import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [Ring β] {abv : β → α} [IsAbsoluteValue abv]

variable [IsComplete β abv]

theorem lim_mul_lim (f g : CauSeq β abv) : CauSeq.lim f * CauSeq.lim g = CauSeq.lim (f * g) := CauSeq.eq_lim_of_const_equiv <|
    show LimZero (const abv (CauSeq.lim f * CauSeq.lim g) - f * g) by
      have h :
        const abv (CauSeq.lim f * CauSeq.lim g) - f * g =
          (const abv (CauSeq.lim f) - f) * g + const abv (CauSeq.lim f) * (const abv (CauSeq.lim g) - g) := by
              apply Subtype.ext
              rw [coe_add]
              simp [sub_mul, mul_sub]
      rw [h]
      exact
        add_limZero (mul_limZero_left _ (Setoid.symm (CauSeq.equiv_lim _)))
          (mul_limZero_right _ (Setoid.symm (CauSeq.equiv_lim _)))

