import Mathlib

variable [GroupWithZero A] [GroupWithZero B] [MonoidWithZeroHomClass F A B] {f}

theorem valueGroup_eq_range : Units.val '' (MonoidWithZeroHom.valueGroup f) = (range f \ {0}) := by
  ext x
  simp only [mem_diff, mem_range, mem_singleton_iff, ← valueMonoid_eq_valueGroup' f, mem_image,
    SetLike.mem_coe, MonoidWithZeroHom.mem_valueMonoid_iff, mem_preimage, mem_range]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [Units.ne_zero, not_false_eq_true, and_true, hy]
  · rintro ⟨⟨y, hy⟩, hx₀⟩
    refine ⟨Units.mk0 x hx₀, ?_, rfl⟩
    simpa [Units.val_mk0, mem_range] using ⟨y, hy⟩

