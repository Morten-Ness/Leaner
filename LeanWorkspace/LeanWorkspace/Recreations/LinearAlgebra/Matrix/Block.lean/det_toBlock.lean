import Mathlib

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [CommRing R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]

theorem det_toBlock (M : Matrix m m R) (p : m → Prop) [DecidablePred p] :
    M.det =
      (fromBlocks (toBlock M p p) (toBlock M p fun j => ¬p j) (toBlock M (fun j => ¬p j) p) <|
          toBlock M (fun j => ¬p j) fun j => ¬p j).det := by
  rw [← Matrix.det_reindex_self (Equiv.sumCompl p).symm M]
  rw [det_apply', det_apply']
  congr; ext σ; congr; ext x
  generalize hy : σ x = y
  cases x <;> cases y <;>
    simp only [Matrix.reindex_apply, toBlock_apply, Equiv.symm_symm, Equiv.sumCompl_apply_inr,
      Equiv.sumCompl_apply_inl, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.submatrix_apply]

