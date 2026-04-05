import Mathlib

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [CommRing R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]

theorem det_matrixOfPolynomials {n : ℕ} (p : Fin n → R[Polynomial.X])
    (h_deg : ∀ i, (p i).natDegree = i) (h_monic : ∀ i, Polynomial.Monic <| p i) :
    (Matrix.of (fun (i j : Fin n) => (p j).coeff i)).det = 1 := by
  rw [Matrix.det_of_upperTriangular (Matrix.matrixOfPolynomials_blockTriangular p (fun i ↦
      Nat.le_of_eq (h_deg i)))]
  convert prod_const_one with x _
  rw [Matrix.of_apply, ← h_deg, coeff_natDegree, (h_monic x).leadingCoeff]

