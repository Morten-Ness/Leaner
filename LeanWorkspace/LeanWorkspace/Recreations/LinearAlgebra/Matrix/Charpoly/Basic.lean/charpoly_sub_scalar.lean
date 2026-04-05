import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

set_option backward.isDefEq.respectTransparency false in
theorem charpoly_sub_scalar (M : Matrix n n R) (μ : R) :
    (M - Matrix.scalar n μ).charpoly = M.charpoly.comp (Polynomial.X + Polynomial.C μ) := by
  simp_rw [Matrix.charpoly, Matrix.det_apply, Polynomial.sum_comp, Polynomial.smul_comp, Polynomial.prod_comp]
  congr! with σ _ i _
  by_cases hi : σ i = i <;> simp [hi]
  ring

