import Mathlib

variable {R K : Type*}

theorem IsNNRat.natFloor {R : Type*} [Semifield R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorSemiring R] (r : R) (n d : ℕ) (h : IsNNRat r n d) (res : ℕ) (hres : n / d = res) :
    IsNat ⌊r⌋₊ res := by
  constructor
  rw [← hres, h.to_eq rfl rfl, Nat.floor_div_eq_div, Nat.cast_id]

