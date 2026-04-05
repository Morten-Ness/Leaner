import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Field α] [LinearOrder α]

variable (β) [IsStrictOrderedRing α] [Field β] [LinearOrder β] [IsStrictOrderedRing β]
  {a a₁ a₂ : α} {b : β} {q : ℚ}

variable [Archimedean α]

omit [LinearOrder β] [IsStrictOrderedRing β] in
theorem cutMap_nonempty (a : α) : (LinearOrderedField.cutMap β a).Nonempty := Nonempty.image _ <| exists_rat_lt a

