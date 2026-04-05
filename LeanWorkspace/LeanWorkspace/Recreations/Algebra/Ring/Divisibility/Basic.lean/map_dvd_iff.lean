import Mathlib

variable {α β : Type*}

variable [Semigroup α] [Semigroup β] {F : Type*} [EquivLike F α β] [MulEquivClass F α β]

theorem map_dvd_iff (f : F) {a b} : f a ∣ f b ↔ a ∣ b := let f := MulEquivClass.toMulEquiv f
  ⟨fun h ↦ by rw [← f.left_inv a, ← f.left_inv b]; exact map_dvd f.symm h, map_dvd f⟩

