import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem fract_eq_iff {a b : R} : fract a = b ↔ 0 ≤ b ∧ b < 1 ∧ ∃ z : ℤ, a - b = z := ⟨fun h => by
    rw [← h]
    exact ⟨Int.fract_nonneg _, Int.fract_lt_one _, ⟨⌊a⌋, sub_sub_cancel _ _⟩⟩,
   by
    rintro ⟨h₀, h₁, z, hz⟩
    rw [← Int.self_sub_floor, eq_comm, eq_sub_iff_add_eq, add_comm, ← eq_sub_iff_add_eq, hz,
      Int.cast_inj, Int.floor_eq_iff, ← hz]
    constructor <;> simpa [sub_eq_add_neg, add_assoc] ⟩

