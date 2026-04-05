import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charpoly_of_upperTriangular [LinearOrder n] (M : Matrix n n R) (h : M.BlockTriangular id) :
    M.charpoly = ∏ i : n, (X - C (M i i)) := by
  simp [Matrix.charpoly, det_of_upperTriangular h.charmatrix]

-- This proof follows http://drorbn.net/AcademicPensieve/2015-12/CayleyHamilton.pdf

