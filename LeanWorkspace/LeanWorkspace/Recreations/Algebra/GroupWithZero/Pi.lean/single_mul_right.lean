import Mathlib

variable {ι : Type*} {α : ι → Type*}

variable [∀ i, MulZeroClass (α i)] [DecidableEq ι] {i : ι} {f : ∀ i, α i}

theorem single_mul_right (a : α i) : single i (f i * a) = f * single i a := funext fun _ ↦ Pi.single_mul_right_apply _ _ _ _

