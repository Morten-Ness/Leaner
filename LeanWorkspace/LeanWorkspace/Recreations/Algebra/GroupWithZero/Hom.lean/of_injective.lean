import Mathlib

variable {F α β : Type*} [Zero α] [Zero β] [FunLike F α β] [ZeroHomClass F α β] {a : α}

theorem of_injective {f : F} (hf : Function.Injective f) [NeZero a] : NeZero (f a) := ⟨by rw [← ZeroHomClass.map_zero f]; exact hf.ne NeZero.out⟩

