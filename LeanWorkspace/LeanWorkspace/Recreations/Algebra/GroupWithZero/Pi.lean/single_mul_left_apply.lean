import Mathlib

variable {ι : Type*} {α : ι → Type*}

variable [∀ i, MulZeroClass (α i)] [DecidableEq ι] {i : ι} {f : ∀ i, α i}

theorem single_mul_left_apply (i j : ι) (a : α i) (f : ∀ i, α i) :
    single i (a * f i) j = single i a j * f j := (apply_single (fun i ↦ (· * f i)) (fun _ ↦ zero_mul _) _ _ _).symm

