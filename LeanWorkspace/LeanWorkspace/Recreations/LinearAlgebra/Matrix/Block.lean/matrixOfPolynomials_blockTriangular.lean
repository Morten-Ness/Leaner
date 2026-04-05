import Mathlib

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [CommRing R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]

theorem matrixOfPolynomials_blockTriangular {R} [Semiring R] {n : ℕ} (p : Fin n → R[Polynomial.X])
    (h_deg : ∀ i, (p i).natDegree ≤ i) :
    Matrix.BlockTriangular (Matrix.of (fun (i j : Fin n) => (p j).coeff i)) id := fun _ j h => by
    exact coeff_eq_zero_of_natDegree_lt <| Nat.lt_of_le_of_lt (h_deg j) h

