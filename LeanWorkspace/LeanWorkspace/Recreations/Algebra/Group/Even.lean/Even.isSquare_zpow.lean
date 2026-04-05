import Mathlib

variable {F α β : Type*}

theorem Even.isSquare_zpow [Group α] {n : ℤ} : Even n → ∀ a : α, IsSquare (a ^ n) := by
  aesop (add simp zpow_add)

example {G : Type*} [CommGroup G] {a b c d e : G} (ha : IsSquare a) {n : ℕ} {k : ℤ} (hk : Even k) :
    IsSquare <| a * (b * b) / (c ^ 2) * (d ^ k) * (e ^ (n + n)) := by aesop

example {G : Type*} [AddCommGroup G] {a b c d e : G} (ha : Even a) {n : ℕ} {k : ℤ} (hk : Even k) :
    Even <| a + (b + b) - 2 • c + k • d + (n + n) • e := by aesop

