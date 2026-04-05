import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Semiring R]

theorem eRank_submatrix_le (A : Matrix m n R) (r : m₀ → m) (c : n₀ → n) :
    (A.submatrix r c).eRank ≤ A.eRank := by
  simpa using OrderHom.mono (β := ℕ∞) Cardinal.toENat <| Matrix.lift_cRank_submatrix_le A r c

