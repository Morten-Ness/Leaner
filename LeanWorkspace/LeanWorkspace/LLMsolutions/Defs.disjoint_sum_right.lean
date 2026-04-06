import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

theorem disjoint_sum_right {a : Multiset α} {i : Multiset (Multiset α)} :
    Disjoint a i.sum ↔ ∀ b ∈ i, Disjoint a b := by
  induction i using Multiset.induction_on with
  | empty =>
      simp [Disjoint, le_bot_iff]
  | @cons b i ih =>
      simp [Multiset.sum_cons, ih, disjoint_iff]
