import Mathlib

variable {α : Type u}

variable [MulOneClass α]

variable [PartialOrder α] [CanonicallyOrderedMul α] {a b c : α}

theorem exists_one_lt_mul_of_lt (h : a < b) : ∃ (c : _) (_ : 1 < c), a * c = b := by
  obtain ⟨c, hc⟩ := le_iff_exists_mul.1 h.le
  refine ⟨c, one_lt_iff_ne_one.2 ?_, hc.symm⟩
  rintro rfl
  simp [hc] at h

