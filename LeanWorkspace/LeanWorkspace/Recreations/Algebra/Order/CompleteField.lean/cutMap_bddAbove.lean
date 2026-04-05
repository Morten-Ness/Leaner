import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Field α] [LinearOrder α]

variable (β) [IsStrictOrderedRing α] [Field β] [LinearOrder β] [IsStrictOrderedRing β]
  {a a₁ a₂ : α} {b : β} {q : ℚ}

variable [Archimedean α]

theorem cutMap_bddAbove (a : α) : BddAbove (LinearOrderedField.cutMap β a) := by
  obtain ⟨q, hq⟩ := exists_rat_gt a
  exact ⟨q, forall_mem_image.2 fun r hr => mod_cast (hq.trans' hr).le⟩

