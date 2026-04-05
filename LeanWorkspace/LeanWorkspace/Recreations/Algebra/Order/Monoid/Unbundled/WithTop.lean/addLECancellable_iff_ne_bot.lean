import Mathlib

variable {α : Type u} {β : Type v}

variable [Add α] {w x y z : WithBot α} {a b : α}

theorem addLECancellable_iff_ne_bot [Nonempty α] [Preorder α]
    [AddLeftReflectLE α] : AddLECancellable x ↔ x ≠ ⊥ where
  mp := by rintro h rfl; exact (bot_lt_coe <| Classical.arbitrary _).not_ge <| h <| by simp
  mpr := WithBot.addLECancellable_of_ne_bot

