import Mathlib

variable {ι α M N : Type*}

variable [Monoid M]

theorem prod_lt_prod' [Preorder M] [MulLeftStrictMono M]
    [MulLeftMono M] [MulRightStrictMono M]
    [MulRightMono M] {l : List ι} (f g : ι → M)
    (h₁ : ∀ i ∈ l, f i ≤ g i) (h₂ : ∃ i ∈ l, f i < g i) : (l.map f).prod < (l.map g).prod := by
  induction l with
  | nil => simp at h₂
  | cons i l ihl =>
    simp only [forall_mem_cons, map_cons, prod_cons] at h₁ ⊢
    simp only [mem_cons, exists_eq_or_imp] at h₂
    cases h₂
    · exact mul_lt_mul_of_lt_of_le ‹_› (List.prod_le_prod' h₁.2)
    · exact mul_lt_mul_of_le_of_lt h₁.1 <| ihl h₁.2 ‹_›

