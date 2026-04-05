import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [Ring β] {abv : β → α} [IsAbsoluteValue abv]

variable [IsComplete β abv]

theorem lim_eq_zero_iff (f : CauSeq β abv) : CauSeq.lim f = 0 ↔ LimZero f := ⟨fun h => by
    have hf := CauSeq.equiv_lim f
    rw [h] at hf
    exact (limZero_congr hf).mpr (const_limZero.mpr rfl),
   fun h => by
    have h₁ : f = f - const abv 0 := ext fun n => by simp
    rw [h₁] at h
    exact CauSeq.lim_eq_of_equiv_const h⟩

