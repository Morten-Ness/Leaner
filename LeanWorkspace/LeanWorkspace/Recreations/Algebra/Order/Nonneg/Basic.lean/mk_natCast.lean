import Mathlib

variable {α : Type*}

variable [AddMonoidWithOne α] [PartialOrder α] [AddLeftMono α] [ZeroLEOneClass α]

theorem mk_natCast (n : ℕ) : (⟨n, n.cast_nonneg'⟩ : { x : α // 0 ≤ x }) = n := rfl

