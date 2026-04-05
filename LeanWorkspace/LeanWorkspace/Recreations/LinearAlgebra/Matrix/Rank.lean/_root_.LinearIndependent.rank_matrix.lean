import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Fintype n] [Fintype o]

theorem _root_.LinearIndependent.rank_matrix [Field R] [Fintype m]
    {M : Matrix m n R} (h : LinearIndependent R M.row) : M.rank = Fintype.card m := by
  rw [M.rank_eq_finrank_span_row, linearIndependent_iff_card_eq_finrank_span.mp h, Set.finrank]

