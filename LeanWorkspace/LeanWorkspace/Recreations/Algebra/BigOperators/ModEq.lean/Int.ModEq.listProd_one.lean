import Mathlib

variable {α : Type*} {n : ℤ} {l : List α} {f g : α → ℤ}

theorem listProd_one {l : List ℤ} (h : ∀ x ∈ l, x ≡ 1 [ZMOD n]) : Nat.ModEq.prod l ≡ 1 [ZMOD n] := by
  simpa using Int.ModEq.listProd_map_one h

