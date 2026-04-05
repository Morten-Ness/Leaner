import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

theorem disjoint_list_sum_left {a : Multiset α} {l : List (Multiset α)} :
    Disjoint l.sum a ↔ ∀ b ∈ l, Disjoint b a := by
  induction l with
  | nil =>
    simp only [zero_disjoint, List.not_mem_nil, IsEmpty.forall_iff, forall_const, List.sum_nil]
  | cons b bs ih =>
    simp [ih]

