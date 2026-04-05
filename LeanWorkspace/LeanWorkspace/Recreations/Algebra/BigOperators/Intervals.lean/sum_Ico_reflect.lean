import Mathlib

variable {α G M : Type*}

variable [CommMonoid M] {s₂ s₁ s : Finset α} {a : α} {g f : α → M}

theorem sum_Ico_reflect {δ : Type*} [AddCommMonoid δ] (f : ℕ → δ) (k : ℕ) {m n : ℕ}
    (h : m ≤ n + 1) : (∑ j ∈ Ico k m, f (n - j)) = ∑ j ∈ Ico (n + 1 - m) (n + 1 - k), f j := @Finset.prod_Ico_reflect (Multiplicative δ) _ f k m n h

