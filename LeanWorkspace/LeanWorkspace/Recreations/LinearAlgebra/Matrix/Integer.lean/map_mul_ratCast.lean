import Mathlib

variable {m n : Type*} [Fintype m] [Fintype n]

theorem map_mul_ratCast {α : Type*} [DivisionRing α] [CharZero α] (A B : Matrix n n ℚ) :
    map (A * B) ((↑) : ℚ → α) = map A (↑) * map B (↑) := Matrix.map_mul (f := Rat.castHom α)

