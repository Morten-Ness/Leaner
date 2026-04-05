import Mathlib

variable {α : Type u} {β : Type v}

variable [Add α] {w x y z : WithBot α} {a b : α}

theorem map_add {F} [Add β] [FunLike F α β] [AddHomClass F α β]
    (f : F) (a b : WithBot α) :
    (a + b).map f = a.map f + b.map f := by
  induction a
  · exact (bot_add _).symm
  · induction b
    · exact (add_bot _).symm
    · rw [map_coe, map_coe, ← coe_add, ← coe_add, ← WithTop.map_add]
      rfl

