import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem mk_le_mk_iff_lt (ha : a ≠ 1) : MulArchimedeanClass.mk a ≤ MulArchimedeanClass.mk b ↔ ∃ n, |b|ₘ < |a|ₘ ^ n := by
  refine ⟨fun ⟨n, hn⟩ ↦ ⟨n + 1, hn.trans_lt ?_⟩, fun ⟨n, hn⟩ ↦ ?_⟩
  · rw [pow_succ]
    exact lt_mul_of_one_lt_right' _ (one_lt_mabs.mpr ha)
  · exact ⟨n, hn.le⟩

