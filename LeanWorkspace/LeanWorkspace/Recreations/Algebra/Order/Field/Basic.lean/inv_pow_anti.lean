import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}

variable [IsStrictOrderedRing α]

theorem inv_pow_anti (a1 : 1 ≤ a) : Antitone fun n : ℕ => (a ^ n)⁻¹ := fun _ _ =>
  inv_pow_le_inv_pow_of_le a1

