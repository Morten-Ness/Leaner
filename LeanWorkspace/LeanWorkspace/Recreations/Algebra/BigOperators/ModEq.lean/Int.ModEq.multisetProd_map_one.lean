import Mathlib

variable {α : Type*} {n : ℤ} {l : List α} {f g : α → ℤ}

theorem multisetProd_map_one {s : Multiset α} (h : ∀ x ∈ s, f x ≡ 1 [ZMOD n]) :
    Nat.ModEq.prod (s.map f) ≡ 1 [ZMOD n] := by
  simpa using Int.ModEq.multisetProd_map h

