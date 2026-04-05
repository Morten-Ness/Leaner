import Mathlib

variable {α β : Type*}

variable [Semigroup α] [Semigroup β] {F : Type*} [EquivLike F α β] [MulEquivClass F α β]

theorem map_dvd_iff_dvd_symm (f : F) {a : α} {b : β} :
    f a ∣ b ↔ a ∣ (MulEquivClass.toMulEquiv f).symm b := by
  obtain ⟨c, rfl⟩ : ∃ c, f c = b := EquivLike.surjective f b
  simp [map_dvd_iff]

