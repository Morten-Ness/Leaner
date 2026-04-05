import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) {L' : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable (I J : LieIdeal R L) {f : L' →ₗ⁅R⁆ L}

theorem derivedSeries_map_eq (k : ℕ) (h : Function.Surjective f) :
    (derivedSeries R L' k).map f = derivedSeries R L k := by
  induction k with
  | zero =>
    change (⊤ : LieIdeal R L').map f = ⊤
    rw [← f.idealRange_eq_map]
    exact f.idealRange_eq_top_of_surjective h
  | succ k ih => simp only [LieAlgebra.derivedSeries_def, map_bracket_eq f h, ih, LieAlgebra.derivedSeriesOfIdeal_succ]

