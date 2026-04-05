import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [AddCommMonoid M] [PartialOrder M] [Sub M] [OrderedSub M] [AddLeftMono M]
  [AddLeftReflectLE M] [ExistsAddOfLE M]

theorem sum_range_tsub {f : ℕ → M} (h : Monotone f) (n : ℕ) :
    ∑ i ∈ range n, (f (i + 1) - f i) = f n - f 0 := by
  apply sum_range_induction
  case base => apply tsub_eq_of_eq_add; rw [zero_add]
  case step =>
    intro n _
    have h₁ : f n ≤ f (n + 1) := h (Nat.le_succ _)
    have h₂ : f 0 ≤ f n := h (Nat.zero_le _)
    rw [tsub_add_eq_add_tsub h₂, add_tsub_cancel_of_le h₁]

