import Mathlib

open scoped Matrix

variable (n p q l : Type*) (R : Type u₂)

variable [DecidableEq n] [DecidableEq p] [DecidableEq q] [DecidableEq l]

variable [CommRing R]

variable [Fintype p] [Fintype q]

theorem pso_inv {i : R} (hi : i * i = -1) : LieAlgebra.Orthogonal.Pso p q R i * LieAlgebra.Orthogonal.Pso p q R (-i) = 1 := by
  ext (x y); rcases x with ⟨x⟩ | ⟨x⟩ <;> rcases y with ⟨y⟩ | ⟨y⟩
  · -- x y : p
    by_cases h : x = y <;>
    simp [LieAlgebra.Orthogonal.Pso, h, one_apply]
  · -- x : p, y : q
    simp [LieAlgebra.Orthogonal.Pso]
  · -- x : q, y : p
    simp [LieAlgebra.Orthogonal.Pso]
  · -- x y : q
    by_cases h : x = y <;>
    simp [LieAlgebra.Orthogonal.Pso, h, hi, one_apply]

