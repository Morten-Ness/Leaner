import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem fract_eq_fract {a b : R} : fract a = fract b ↔ ∃ z : ℤ, a - b = z := ⟨fun h => ⟨⌊a⌋ - ⌊b⌋, by unfold fract at h; rw [Int.cast_sub, sub_eq_sub_iff_sub_eq_sub.1 h]⟩,
   by
    rintro ⟨z, hz⟩
    refine Int.fract_eq_iff.2 ⟨Int.fract_nonneg _, Int.fract_lt_one _, z + ⌊b⌋, ?_⟩
    rw [eq_add_of_sub_eq hz, add_comm, Int.cast_add]
    exact add_sub_sub_cancel _ _ _⟩

