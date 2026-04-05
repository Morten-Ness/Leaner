import Mathlib

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

theorem prod_set :
    ∀ (L : List M) (n : ℕ) (a : M),
      (L.set n a).prod =
        ((L.take n).prod * if n < L.length then a else 1) * (L.drop (n + 1)).prod
  | x :: xs, 0, a => by simp [set]
  | x :: xs, i + 1, a => by simp [set, prod_set xs i a, mul_assoc]
  | [], _, _ => by simp [set]
