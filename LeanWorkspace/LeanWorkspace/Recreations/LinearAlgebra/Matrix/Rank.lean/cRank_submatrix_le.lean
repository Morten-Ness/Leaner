import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Semiring R]

theorem cRank_submatrix_le {m m₀ : Type um} (A : Matrix m n R) (r : m₀ → m) (c : n₀ → n) :
    (A.submatrix r c).cRank ≤ A.cRank := by
  simpa using Matrix.lift_cRank_submatrix_le A r c

