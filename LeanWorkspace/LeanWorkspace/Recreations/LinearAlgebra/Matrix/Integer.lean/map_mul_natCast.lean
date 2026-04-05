import Mathlib

variable {m n : Type*} [Fintype m] [Fintype n]

theorem map_mul_natCast {α : Type*} [NonAssocSemiring α] (A B : Matrix n n ℕ) :
    map (A * B) ((↑) : ℕ → α) = map A (↑) * map B (↑) := Matrix.map_mul (f := Nat.castRingHom α)

