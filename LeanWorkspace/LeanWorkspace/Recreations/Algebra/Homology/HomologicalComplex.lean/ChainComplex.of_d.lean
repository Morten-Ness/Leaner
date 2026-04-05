import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {V} {α : Type*} [AddRightCancelSemigroup α] [One α] [DecidableEq α]

variable (X : α → V) (d : ∀ n, X (n + 1) ⟶ X n) (sq : ∀ n, d (n + 1) ≫ d n = 0)

theorem of_d (j : α) : (ChainComplex.of X d sq).d (j + 1) j = d j := by
  dsimp [ChainComplex.of]
  rw [if_pos rfl, Category.id_comp]

