import Mathlib

variable {α : Type*} {n : ℤ} {l : List α} {f g : α → ℤ}

theorem prod_one {s : Finset α} (h : ∀ x ∈ s, f x ≡ 1 [ZMOD n]) : ∏ x ∈ s, f x ≡ 1 [ZMOD n] := by
  simpa using Int.ModEq.prod h

