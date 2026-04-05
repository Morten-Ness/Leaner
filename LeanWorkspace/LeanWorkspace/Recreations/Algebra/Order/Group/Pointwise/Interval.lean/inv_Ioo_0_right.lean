import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}

theorem inv_Ioo_0_right {a : α} (ha : a < 0) : (Ioo a 0)⁻¹ = Iio a⁻¹ := by
  ext x
  refine ⟨fun h ↦ (lt_inv_of_neg (inv_neg''.1 h.2) ha).2 h.1, fun h ↦ ?_⟩
  have h' := (h.trans (inv_neg''.2 ha))
  exact ⟨(lt_inv_of_neg ha h').2 h, inv_neg''.2 h'⟩

