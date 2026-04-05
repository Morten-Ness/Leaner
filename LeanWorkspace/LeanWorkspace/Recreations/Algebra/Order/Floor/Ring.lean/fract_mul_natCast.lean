import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem fract_mul_natCast (a : R) (b : ℕ) : ∃ z : ℤ, fract a * b - fract (a * b) = z := by
  induction b with
  | zero => use 0; simp
  | succ c hc =>
    rcases hc with ⟨z, hz⟩
    rw [Nat.cast_add, mul_add, mul_add, Nat.cast_one, mul_one, mul_one]
    rcases Int.fract_add (a * c) a with ⟨y, hy⟩
    use z - y
    rw [Int.cast_sub, ← hz, ← hy]
    abel

