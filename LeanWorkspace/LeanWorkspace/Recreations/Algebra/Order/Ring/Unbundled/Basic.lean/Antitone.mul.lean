import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [Preorder R] {a b c d : R}

variable [Preorder α] {f g : α → R}

theorem Antitone.mul [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Antitone f) (hg : Antitone g) (hf₀ : ∀ x, f x ≤ 0) (hg₀ : ∀ x, g x ≤ 0) :
    Monotone (f * g) := fun _ _ h => mul_le_mul_of_nonpos_of_nonpos (hf h) (hg h) (hf₀ _) (hg₀ _)

