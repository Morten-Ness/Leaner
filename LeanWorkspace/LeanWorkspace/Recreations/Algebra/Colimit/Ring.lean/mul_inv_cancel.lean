import Mathlib

variable {ι : Type*} [Preorder ι] (G : ι → Type*)

variable [Nonempty ι] [IsDirectedOrder ι] [∀ i, Field (G i)]

variable (f : ∀ i j, i ≤ j → G i → G j)

variable (f' : ∀ i j, i ≤ j → G i →+* G j)

theorem mul_inv_cancel {p : Ring.DirectLimit G f} (hp : p ≠ 0) : p * Field.DirectLimit.inv G f p = 1 := by
  rw [Field.DirectLimit.inv, dif_neg hp, Classical.choose_spec (Field.DirectLimit.exists_inv G f hp)]

