import Mathlib

variable {ι α M N : Type*}

variable [Monoid M]

theorem SublistForall₂.prod_le_prod' [Preorder M]
    [MulRightMono M] [MulLeftMono M]
    {l₁ l₂ : List M} (h : SublistForall₂ (· ≤ ·) l₁ l₂) (h₁ : ∀ a ∈ l₂, (1 : M) ≤ a) :
    l₁.prod ≤ l₂.prod := let ⟨_, hall, hsub⟩ := sublistForall₂_iff.1 h
  hall.prod_le_prod'.trans <| hsub.prod_le_prod' h₁

