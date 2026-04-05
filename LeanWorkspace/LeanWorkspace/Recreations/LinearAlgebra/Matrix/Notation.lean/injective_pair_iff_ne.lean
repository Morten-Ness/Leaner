import Mathlib

theorem injective_pair_iff_ne {α : Type*} {x y : α} :
    Function.Injective ![x, y] ↔ x ≠ y := by
  refine ⟨fun h ↦ ?_, fun h a b h' ↦ ?_⟩
  · simpa using h.ne Fin.zero_ne_one
  · fin_cases a <;> fin_cases b <;> aesop

