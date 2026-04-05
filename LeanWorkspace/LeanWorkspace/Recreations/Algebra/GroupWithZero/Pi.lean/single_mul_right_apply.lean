import Mathlib

variable {ι : Type*} {α : ι → Type*}

variable [∀ i, MulZeroClass (α i)] [DecidableEq ι] {i : ι} {f : ∀ i, α i}

theorem single_mul_right_apply (i j : ι) (f : ∀ i, α i) (a : α i) :
    single i (f i * a) j = f j * single i a j := (apply_single (f · * ·) (fun _ ↦ mul_zero _) _ _ _).symm

