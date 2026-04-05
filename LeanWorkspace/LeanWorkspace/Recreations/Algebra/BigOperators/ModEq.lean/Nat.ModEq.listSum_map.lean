import Mathlib

variable {α : Type*} {n : ℕ} {l : List α} {f g : α → ℕ}

theorem listSum_map (h : ∀ x ∈ l, f x ≡ g x [MOD n]) : (l.map f).sum ≡ (l.map g).sum [MOD n] := by
  induction l <;> aesop (add unsafe Nat.ModEq.add)

