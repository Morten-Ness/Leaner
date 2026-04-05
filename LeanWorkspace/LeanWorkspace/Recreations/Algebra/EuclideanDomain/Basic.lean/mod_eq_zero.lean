import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

theorem mod_eq_zero {a b : R} : a % b = 0 ↔ b ∣ a := ⟨fun h => by
    rw [← div_add_mod a b, h, add_zero]
    exact dvd_mul_right _ _, fun ⟨c, e⟩ => by
    rw [e, ← add_left_cancel_iff, div_add_mod, add_zero]
    haveI := Classical.dec
    by_cases b0 : b = 0
    · simp only [b0, zero_mul]
    · rw [mul_div_cancel_left₀ _ b0]⟩

