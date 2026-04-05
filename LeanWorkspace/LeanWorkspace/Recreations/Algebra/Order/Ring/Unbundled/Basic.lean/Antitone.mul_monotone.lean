import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [Preorder R] {a b c d : R}

variable [Preorder α] {f g : α → R}

theorem Antitone.mul_monotone [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Antitone f) (hg : Monotone g) (hf₀ : ∀ x, f x ≤ 0)
    (hg₀ : ∀ x, 0 ≤ g x) : Antitone (f * g) := fun _ _ h =>
  mul_le_mul_of_nonpos_of_nonneg (hf h) (hg h) (hf₀ _) (hg₀ _)

