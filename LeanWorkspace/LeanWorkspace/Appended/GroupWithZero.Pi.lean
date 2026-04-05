import Mathlib

section

variable {ι : Type*} {α : ι → Type*}

variable [∀ i, MulZeroClass (α i)] [DecidableEq ι] {i : ι} {f : ∀ i, α i}

theorem single_mul_left (a : α i) : single i (a * f i) = single i a * f := funext fun _ ↦ Pi.single_mul_left_apply _ _ _ _

end

section

variable {ι : Type*} {α : ι → Type*}

variable [∀ i, MulZeroClass (α i)] [DecidableEq ι] {i : ι} {f : ∀ i, α i}

theorem single_mul_left_apply (i j : ι) (a : α i) (f : ∀ i, α i) :
    single i (a * f i) j = single i a j * f j := (apply_single (fun i ↦ (· * f i)) (fun _ ↦ zero_mul _) _ _ _).symm

end

section

variable {ι : Type*} {α : ι → Type*}

variable [∀ i, MulZeroClass (α i)] [DecidableEq ι] {i : ι} {f : ∀ i, α i}

theorem single_mul_right (a : α i) : single i (f i * a) = f * single i a := funext fun _ ↦ Pi.single_mul_right_apply _ _ _ _

end

section

variable {ι : Type*} {α : ι → Type*}

variable [∀ i, MulZeroClass (α i)] [DecidableEq ι] {i : ι} {f : ∀ i, α i}

theorem single_mul_right_apply (i j : ι) (f : ∀ i, α i) (a : α i) :
    single i (f i * a) j = f j * single i a j := (apply_single (f · * ·) (fun _ ↦ mul_zero _) _ _ _).symm

end
