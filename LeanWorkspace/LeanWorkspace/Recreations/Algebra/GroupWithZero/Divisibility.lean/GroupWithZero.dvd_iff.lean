import Mathlib

variable {α : Type*}

variable [GroupWithZero α]

theorem GroupWithZero.dvd_iff {m n : α} : m ∣ n ↔ (m = 0 → n = 0) := by
  refine ⟨fun ⟨a, ha⟩ hm => ?_, fun h => ?_⟩
  · simp [hm, ha]
  · refine ⟨m⁻¹ * n, ?_⟩
    obtain rfl | hn := eq_or_ne n 0
    · simp
    · rw [mul_inv_cancel_left₀ (mt h hn)]

