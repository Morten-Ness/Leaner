import Mathlib

open scoped Matrix

variable (n p q l : Type*) (R : Type u₂)

variable [DecidableEq n] [DecidableEq p] [DecidableEq q] [DecidableEq l]

variable [CommRing R]

variable [Fintype p] [Fintype q]

variable [Fintype l]

theorem indefiniteDiagonal_assoc :
    LieAlgebra.Orthogonal.indefiniteDiagonal (Unit ⊕ l) l R =
      Matrix.reindexLieEquiv (Equiv.sumAssoc Unit l l).symm
        (Matrix.fromBlocks 1 0 0 (LieAlgebra.Orthogonal.indefiniteDiagonal l l R)) := by
  ext ⟨⟨i₁ | i₂⟩ | i₃⟩ ⟨⟨j₁ | j₂⟩ | j₃⟩ <;>
    simp only [LieAlgebra.Orthogonal.indefiniteDiagonal, Matrix.diagonal_apply, Equiv.sumAssoc_apply_inl_inl,
      Matrix.reindexLieEquiv_apply, Matrix.submatrix_apply, Equiv.symm_symm, Matrix.reindex_apply,
      Sum.elim_inl, if_true, Matrix.one_apply_eq, Matrix.fromBlocks_apply₁₁,
      Equiv.sumAssoc_apply_inl_inr, if_false, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Equiv.sumAssoc_apply_inr, Sum.elim_inr, Sum.inl_injective.eq_iff,
      Sum.inr_injective.eq_iff, reduceCtorEq] <;>
    congr 1

