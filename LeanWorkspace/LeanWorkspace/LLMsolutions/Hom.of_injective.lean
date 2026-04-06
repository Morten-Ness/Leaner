import Mathlib

variable {F α β : Type*} [Zero α] [Zero β] [FunLike F α β] [ZeroHomClass F α β] {a : α}

theorem of_injective {f : F} (hf : Function.Injective f) [NeZero a] : NeZero (f a) := by
  refine ⟨?_⟩
  intro h
  have : a = 0 := hf (by simpa using h)
  exact NeZero.ne a this
