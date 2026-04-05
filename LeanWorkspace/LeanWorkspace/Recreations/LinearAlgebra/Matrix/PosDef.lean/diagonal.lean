import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

theorem diagonal [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
    {d : n → R} (h : ∀ i, 0 < d i) :
    Matrix.PosDef (diagonal d) where
  left := isHermitian_diagonal_of_self_adjoint _ <| funext fun i => IsSelfAdjoint.of_nonneg (h i).le
  right x hx := by
    refine Finsupp.sum_pos' (fun _ _ ↦ Finsupp.sum_nonneg ?_) ?_
    · simp +contextual [diagonal, apply_ite, star_left_conjugate_nonneg (h _).le]
    obtain ⟨i, hxi⟩ := by simpa [Finsupp.ext_iff] using hx
    refine ⟨i, ?_, Finsupp.sum_pos' ?_ ⟨i, ?_, ?_⟩⟩ <;> simp +contextual [diagonal,
      apply_ite, star_left_conjugate_nonneg (h _).le,
      star_left_conjugate_pos (h i), IsRegular.of_ne_zero hxi, Finsupp.mem_support_iff.mpr hxi]

