import Mathlib

variable {ι : Type*} [Preorder ι] (G : ι → Type*)

variable [Nonempty ι] [IsDirectedOrder ι] [∀ i, Field (G i)]

variable (f : ∀ i j, i ≤ j → G i → G j)

variable (f' : ∀ i j, i ≤ j → G i →+* G j)

theorem inv_mul_cancel {p : Ring.DirectLimit G f} (hp : p ≠ 0) : Field.DirectLimit.inv G f p * p = 1 := by
  rw [_root_.mul_comm, Field.DirectLimit.mul_inv_cancel G f hp]

