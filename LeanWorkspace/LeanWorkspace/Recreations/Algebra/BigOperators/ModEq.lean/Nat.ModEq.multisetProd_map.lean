import Mathlib

variable {α : Type*} {n : ℕ} {l : List α} {f g : α → ℕ}

theorem multisetProd_map {s : Multiset α} (h : ∀ x ∈ s, f x ≡ g x [MOD n]) :
    (s.map f).prod ≡ (s.map g).prod [MOD n] := by
  rcases s with ⟨l⟩
  simpa using Nat.ModEq.listProd_map (l := l) h

