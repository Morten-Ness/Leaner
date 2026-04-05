import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem const_inj {x y : β} : (CauSeq.const x : CauSeq β abv) = CauSeq.const y ↔ x = y := ⟨fun h => congr_arg (fun f : CauSeq β abv => (f : ℕ → β) 0) h, congr_arg _⟩

