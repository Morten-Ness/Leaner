import Mathlib

variable {n : Type*} [DecidableEq n] [Fintype n]

variable {R : Type*} [CommSemiring R]

theorem permanent_diagonal {d : n → R} : Matrix.permanent (diagonal d) = ∏ i, d i := by
  refine (sum_eq_single 1 (fun σ _ hσ ↦ ?_) (fun h ↦ (h <| mem_univ _).elim)).trans ?_
  · match not_forall.mp (mt Equiv.ext hσ) with
    | ⟨x, hx⟩ => exact Finset.prod_eq_zero (mem_univ x) (if_neg hx)
  · simp only [Equiv.Perm.one_apply, diagonal_apply_eq]

