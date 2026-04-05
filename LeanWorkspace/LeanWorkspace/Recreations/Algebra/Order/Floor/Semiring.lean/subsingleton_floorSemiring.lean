import Mathlib

variable {R K : Type*}

theorem subsingleton_floorSemiring {R} [Semiring R] [LinearOrder R] :
    Subsingleton (FloorSemiring R) := by
  refine ⟨fun H₁ H₂ => ?_⟩
  have : H₁.ceil = H₂.ceil := funext fun a => (H₁.gc_ceil.l_unique H₂.gc_ceil) fun n => rfl
  have : H₁.floor = H₂.floor := by
    ext a
    rcases lt_or_ge a 0 with h | h
    · rw [H₁.floor_of_neg, H₂.floor_of_neg] <;> exact h
    · refine eq_of_forall_le_iff fun n => ?_
      rw [H₁.gc_floor, H₂.gc_floor] <;> exact h
  cases H₁
  cases H₂
  congr

