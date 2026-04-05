import Mathlib

variable {m n p R : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

theorem dotProduct_self_eq_zero [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {v : n → R} :
    v ⬝ᵥ v = 0 ↔ v = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (v i)).trans <| by
    simp [funext_iff]

