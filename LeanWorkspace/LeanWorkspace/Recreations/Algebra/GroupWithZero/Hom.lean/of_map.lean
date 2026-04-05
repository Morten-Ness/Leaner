import Mathlib

variable {F α β : Type*} [Zero α] [Zero β] [FunLike F α β] [ZeroHomClass F α β] {a : α}

theorem of_map (f : F) [neZero : NeZero (f a)] : NeZero a := ⟨fun h ↦ ne (f a) <| by rw [h]; exact ZeroHomClass.map_zero f⟩

