import Mathlib

variable {α : Type u} {β : Type v}

variable [Add α] {w x y z : WithBot α} {a b : α}

theorem add_le_add_iff_right' {α : Type*} [Add α] [LE α]
    [AddRightMono α] [AddRightReflectLE α]
    {a b c : WithBot (WithTop α)} (hc : c ≠ ⊥) (hc' : c ≠ ⊤) :
    a + c ≤ b + c ↔ a ≤ b := by
  induction a <;> induction b <;> induction c <;> norm_cast at * <;>
    aesop (add simp WithTop.add_le_add_iff_right)

--  There is no `WithBot.map_mul_of_mulHom`, since `WithBot` does not have a multiplication.

