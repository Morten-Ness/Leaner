import Mathlib

variable {m n : Type*} [Fintype m] [Fintype n]

theorem map_mul_intCast {α : Type*} [NonAssocRing α] (A B : Matrix n n ℤ) :
    map (A * B) ((↑) : ℤ → α) = map A (↑) * map B (↑) := Matrix.map_mul (f := Int.castRingHom α)

