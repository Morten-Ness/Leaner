import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R]
    (a : R) : 0 ≤ a ^ 2 := by
  obtain ha | ha := le_or_gt 0 a
  · exact pow_succ_nonneg ha _
  obtain ⟨b, hab⟩ := exists_add_of_le ha.le
  have hb : 0 < b := not_le.1 fun hb ↦ (add_neg_of_neg_of_nonpos ha hb).ne' hab
  calc
    0 ≤ b ^ 2 := pow_succ_nonneg hb.le _
    _ = b ^ 2 + a * (a + b) := by rw [← hab, mul_zero, add_zero]
    _ = a ^ 2 + (a + b) * b := by rw [add_mul, mul_add, sq, sq, add_comm, add_assoc]
    _ = a ^ 2 := by rw [← hab, zero_mul, add_zero]

