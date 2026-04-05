import Mathlib

variable {α : Type*} {n : ℕ} {l : List α} {f g : α → ℕ}

theorem listProd_map_one (h : ∀ x ∈ l, f x ≡ 1 [MOD n]) : (l.map f).prod ≡ 1 [MOD n] := (Nat.ModEq.listProd_map h).trans <| by simp [Nat.ModEq.refl]

