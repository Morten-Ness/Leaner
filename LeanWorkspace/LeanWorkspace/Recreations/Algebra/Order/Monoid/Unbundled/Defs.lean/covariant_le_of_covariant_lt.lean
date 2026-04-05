import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

theorem covariant_le_of_covariant_lt [PartialOrder N] :
    Covariant M N μ (· < ·) → Covariant M N μ (· ≤ ·) := by
  intro h a b c bc
  rcases bc.eq_or_lt with (rfl | bc)
  · exact le_rfl
  · exact (h _ bc).le

