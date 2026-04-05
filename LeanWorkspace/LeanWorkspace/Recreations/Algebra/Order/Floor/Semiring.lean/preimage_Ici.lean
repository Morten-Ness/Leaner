import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

theorem preimage_Ici {a : R} : (Nat.cast : ℕ → R) ⁻¹' Set.Ici a = Set.Ici ⌈a⌉₊ := by
  ext
  simp [ceil_le]

