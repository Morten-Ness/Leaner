import Mathlib

variable {ι α M N : Type*}

variable [Monoid M]

theorem Forall₂.prod_le_prod' [Preorder M] [MulRightMono M]
    [MulLeftMono M] {l₁ l₂ : List M} (h : Forall₂ (· ≤ ·) l₁ l₂) :
    l₁.prod ≤ l₂.prod := by
  induction h with
  | nil => rfl
  | cons hab ih ih' => simpa only [prod_cons] using mul_le_mul' hab ih'

