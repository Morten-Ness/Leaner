import Mathlib

open scoped Pointwise

variable {G : Type*} [CommGroup G] (s : Set G)

theorem mul_stabilizer_self : s * stabilizer G s = s := by rw [mul_comm, MulAction.stabilizer_mul_self]

local notation "Q" => G ⧸ stabilizer G s
local notation "q" => ((↑) : G → Q)

