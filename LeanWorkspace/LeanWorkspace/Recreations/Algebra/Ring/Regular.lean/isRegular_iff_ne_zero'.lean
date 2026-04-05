import Mathlib

variable {α : Type*}

theorem isRegular_iff_ne_zero' [Nontrivial α] [NonUnitalNonAssocRing α] [NoZeroDivisors α]
    {k : α} : IsRegular k ↔ k ≠ 0 := ⟨fun h => by
    rintro rfl
    exact not_not.mpr h.left not_isLeftRegular_zero, .of_ne_zero'⟩

