import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {V} {α : Type*} [AddRightCancelSemigroup α] [One α] [DecidableEq α]

variable (X : α → V) (d : ∀ n, X n ⟶ X (n + 1)) (sq : ∀ n, d n ≫ d (n + 1) = 0)

theorem of_x (n : α) : (CochainComplex.of X d sq).X n = X n := rfl

