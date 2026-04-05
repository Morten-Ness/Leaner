import Mathlib

variable {α : Type*} {n : ℕ} {l : List α} {f g : α → ℕ}

theorem prod_one {s : Finset α} (h : ∀ x ∈ s, f x ≡ 1 [MOD n]) : ∏ x ∈ s, f x ≡ 1 [MOD n] := by
  simpa using Nat.ModEq.prod h

