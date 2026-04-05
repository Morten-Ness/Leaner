import Mathlib

variable {α : Type u} {β : Type v} {R : Type x}

variable [Ring α]

theorem map_neg {F : Type*} [Ring β] [FunLike F α β] [RingHomClass F α β]
    (f : F) (u : αˣ) : map (f : α →* β) (-u) = -map (f : α →* β) u := ext (by simp only [coe_map, Units.val_neg, MonoidHom.coe_coe, map_neg])

