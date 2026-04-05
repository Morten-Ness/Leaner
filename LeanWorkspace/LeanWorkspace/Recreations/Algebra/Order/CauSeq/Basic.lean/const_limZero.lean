import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem const_limZero {x : β} : CauSeq.LimZero (CauSeq.const x) ↔ x = 0 := ⟨fun H =>
    (abv_eq_zero abv).1 <|
      (eq_of_le_of_forall_lt_imp_le_of_dense (abv_nonneg abv _)) fun _ ε0 =>
        let ⟨_, hi⟩ := H _ ε0
        le_of_lt <| hi _ le_rfl,
    fun e => e.symm ▸ CauSeq.zero_limZero⟩

