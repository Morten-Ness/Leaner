import Mathlib

variable {α : Type u} {β : Type v}

variable [Add α] {w x y z : WithTop α} {a b : α}

theorem addLECancellable_iff_ne_top [Nonempty α] [Preorder α]
    [AddLeftReflectLE α] : AddLECancellable x ↔ x ≠ ⊤ where
  mp := by rintro h rfl; exact (coe_lt_top <| Classical.arbitrary _).not_ge <| h <| by simp
  mpr := WithTop.addLECancellable_of_ne_top

--  There is no `WithTop.map_mul_of_mulHom`, since `WithTop` does not have a multiplication.

