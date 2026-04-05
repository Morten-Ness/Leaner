import Mathlib

variable {R K : Type*} [Semiring R] [CommSemiring K] {i : R →+* K}

variable {a b : R} {bi : K}

theorem denomsClearable_zero (N : ℕ) (a : R) (bu : bi * i b = 1) : DenomsClearable a b N 0 i := ⟨0, bi, bu, by
    simp only [eval_zero, map_zero, mul_zero, Polynomial.map_zero]⟩

