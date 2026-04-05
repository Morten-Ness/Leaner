import Mathlib

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem trace_eq_neg_charpoly_coeff [Nonempty n] (M : Matrix n n R) :
    trace M = -M.charpoly.coeff (Fintype.card n - 1) := by
  rw [Matrix.charpoly_coeff_eq_prod_coeff_of_le _ le_rfl, Fintype.card,
    prod_X_sub_C_coeff_card_pred Finset.univ (fun i : n => M i i) Fintype.card_pos, neg_neg, trace]
  simp_rw [diag_apply]

