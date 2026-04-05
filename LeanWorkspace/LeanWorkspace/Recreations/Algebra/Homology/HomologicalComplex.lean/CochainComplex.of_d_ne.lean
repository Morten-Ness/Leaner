import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {V} {α : Type*} [AddRightCancelSemigroup α] [One α] [DecidableEq α]

variable (X : α → V) (d : ∀ n, X n ⟶ X (n + 1)) (sq : ∀ n, d n ≫ d (n + 1) = 0)

set_option backward.isDefEq.respectTransparency false in
theorem of_d_ne {i j : α} (h : i + 1 ≠ j) : (CochainComplex.of X d sq).d i j = 0 := by
  dsimp [CochainComplex.of]
  rw [dif_neg h]

