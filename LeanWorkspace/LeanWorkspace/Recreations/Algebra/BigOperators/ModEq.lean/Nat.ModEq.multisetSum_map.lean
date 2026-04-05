import Mathlib

variable {α : Type*} {n : ℕ} {l : List α} {f g : α → ℕ}

theorem multisetSum_map {s : Multiset α} (h : ∀ x ∈ s, f x ≡ g x [MOD n]) :
    (s.map f).sum ≡ (s.map g).sum [MOD n] := by
  rcases s with ⟨l⟩
  simpa using Nat.ModEq.listSum_map (l := l) h

