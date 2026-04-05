import Mathlib

variable {ι α M N : Type*}

variable [Monoid M]

theorem Sublist.prod_le_prod' [Preorder M] [MulRightMono M]
    [MulLeftMono M] {l₁ l₂ : List M} (h : l₁ <+ l₂)
    (h₁ : ∀ a ∈ l₂, (1 : M) ≤ a) : l₁.prod ≤ l₂.prod := by
  induction h with
  | slnil => rfl
  | cons a _ ih' =>
    simp only [prod_cons, forall_mem_cons] at h₁ ⊢
    exact (ih' h₁.2).trans (le_mul_of_one_le_left' h₁.1)
  | cons₂ a _ ih' =>
    simp only [prod_cons, forall_mem_cons] at h₁ ⊢
    grw [ih' h₁.2]

