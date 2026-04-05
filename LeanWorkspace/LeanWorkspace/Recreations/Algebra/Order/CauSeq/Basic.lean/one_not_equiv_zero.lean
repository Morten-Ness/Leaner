import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] [IsDomain β] (abv : β → α) [IsAbsoluteValue abv]

theorem one_not_equiv_zero : ¬CauSeq.const abv 1 ≈ CauSeq.const abv 0 := fun h =>
  have : ∀ ε > 0, ∃ i, ∀ k, i ≤ k → abv (1 - 0) < ε := h
  have h1 : abv 1 ≤ 0 :=
    le_of_not_gt fun h2 : 0 < abv 1 =>
      (Exists.elim (this _ h2)) fun i hi => lt_irrefl (abv 1) <| by simpa using hi _ le_rfl
  have h2 : 0 ≤ abv 1 := abv_nonneg abv _
  have : abv 1 = 0 := le_antisymm h1 h2
  have : (1 : β) = 0 := (abv_eq_zero abv).mp this
  absurd this one_ne_zero

