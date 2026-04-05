import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [DecidableEq α]

theorem count_sum' {s : Finset ι} {a : α} {f : ι → Multiset α} :
    count a (∑ x ∈ s, f x) = ∑ x ∈ s, count a (f x) := by
  dsimp only [Finset.sum]
  rw [count_sum]

