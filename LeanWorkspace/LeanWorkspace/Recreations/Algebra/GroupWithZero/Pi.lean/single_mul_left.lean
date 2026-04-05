import Mathlib

variable {ι : Type*} {α : ι → Type*}

variable [∀ i, MulZeroClass (α i)] [DecidableEq ι] {i : ι} {f : ∀ i, α i}

theorem single_mul_left (a : α i) : single i (a * f i) = single i a * f := funext fun _ ↦ Pi.single_mul_left_apply _ _ _ _

