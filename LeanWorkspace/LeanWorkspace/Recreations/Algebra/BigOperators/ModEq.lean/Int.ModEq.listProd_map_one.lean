import Mathlib

variable {α : Type*} {n : ℤ} {l : List α} {f g : α → ℤ}

theorem listProd_map_one (h : ∀ x ∈ l, f x ≡ 1 [ZMOD n]) : Nat.ModEq.prod (l.map f) ≡ 1 [ZMOD n] := (Int.ModEq.listProd_map h).trans <| by simp

