import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem eval_charpoly (M : Matrix m m R) (t : R) :
    M.charpoly.eval t = (Matrix.scalar _ t - M).det := by
  rw [Matrix.charpoly, ← Polynomial.coe_evalRingHom, RingHom.map_det, Matrix.charmatrix]
  congr
  ext i j
  obtain rfl | hij := eq_or_ne i j <;> simp [*]

