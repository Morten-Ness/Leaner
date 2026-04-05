import Mathlib

variable {α : Type*} {n : ℕ} {l : List α} {f g : α → ℕ}

theorem listProd_map (h : ∀ x ∈ l, f x ≡ g x [MOD n]) :
    (l.map f).prod ≡ (l.map g).prod [MOD n] := by
  induction l <;> aesop (add unsafe Nat.ModEq.mul)

