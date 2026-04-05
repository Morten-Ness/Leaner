import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}

variable [IsStrictOrderedRing α]

theorem one_div_pow_anti (a1 : 1 ≤ a) : Antitone fun n : ℕ => 1 / a ^ n := fun _ _ =>
  one_div_pow_le_one_div_pow_of_le a1

