import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [Field β] {abv : β → α} [IsAbsoluteValue abv] [IsComplete β abv]

theorem lim_inv {f : CauSeq β abv} (hf : ¬LimZero f) : CauSeq.lim (inv f hf) = (CauSeq.lim f)⁻¹ := have hl : CauSeq.lim f ≠ 0 := by rwa [← CauSeq.lim_eq_zero_iff] at hf
  CauSeq.lim_eq_of_equiv_const <|
    show LimZero (inv f hf - const abv (CauSeq.lim f)⁻¹) from
      have h₁ : ∀ (g f : CauSeq β abv) (hf : ¬LimZero f), LimZero (g - f * inv f hf * g) :=
        fun g f hf => by
          have h₂ : g - f * inv f hf * g = 1 * g - f * inv f hf * g := by rw [one_mul g]
          have h₃ : f * inv f hf * g = (f * inv f hf) * g := by simp [mul_assoc]
          have h₄ : g - f * inv f hf * g = (1 - f * inv f hf) * g := by rw [h₂, h₃, ← sub_mul]
          have h₅ : g - f * inv f hf * g = g * (1 - f * inv f hf) := by rw [h₄, mul_comm]
          have h₆ : g - f * inv f hf * g = g * (1 - inv f hf * f) := by rw [h₅, mul_comm f]
          rw [h₆]; exact mul_limZero_right _ (Setoid.symm (CauSeq.inv_mul_cancel _))
      have h₂ :
        LimZero
          (inv f hf - const abv (CauSeq.lim f)⁻¹ -
            (const abv (CauSeq.lim f) - f) * (inv f hf * const abv (CauSeq.lim f)⁻¹)) := by
              rw [sub_mul, ← sub_add, sub_sub, sub_add_eq_sub_sub, sub_right_comm, sub_add]
              change LimZero
                (inv f hf - const abv (CauSeq.lim f) * (inv f hf * const abv (CauSeq.lim f)⁻¹) -
                  (const abv (CauSeq.lim f)⁻¹ - f * (inv f hf * const abv (CauSeq.lim f)⁻¹)))
              exact sub_limZero
                (by rw [← mul_assoc, mul_right_comm, const_inv hl]; exact h₁ _ _ _)
                (by rw [← mul_assoc]; exact h₁ _ _ _)
      (limZero_congr h₂).mpr <| mul_limZero_left _ (Setoid.symm (CauSeq.equiv_lim f))

