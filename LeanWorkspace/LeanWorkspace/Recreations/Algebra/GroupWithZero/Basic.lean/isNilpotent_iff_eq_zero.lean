import Mathlib

variable {M₀ G₀ : Type*}

variable {R S : Type*} {x y : R}

theorem isNilpotent_iff_eq_zero [MonoidWithZero R] [IsReduced R] : IsNilpotent x ↔ x = 0 := ⟨fun h => h.eq_zero, fun h => h.symm ▸ IsNilpotent.zero⟩

