import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a : R}

variable {S : Type*} [Semiring S] [LinearOrder S] [FloorSemiring S] {b : S}

theorem ceil_congr (h : ∀ n : ℕ, a ≤ n ↔ b ≤ n) : ⌈a⌉₊ = ⌈b⌉₊ := (ceil_le.2 <| (h _).2 <| Nat.le_ceil _).antisymm <| ceil_le.2 <| (h _).1 <| Nat.le_ceil _

