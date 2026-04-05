import Mathlib

open scoped Matrix

variable (n p q l : Type*) (R : Type u₂)

variable [DecidableEq n] [DecidableEq p] [DecidableEq q] [DecidableEq l]

variable [CommRing R]

variable [Fintype p] [Fintype q]

theorem indefiniteDiagonal_transform {i : R} (hi : i * i = -1) :
    (LieAlgebra.Orthogonal.Pso p q R i)ᵀ * LieAlgebra.Orthogonal.indefiniteDiagonal p q R * LieAlgebra.Orthogonal.Pso p q R i = 1 := by
  ext (x y); rcases x with ⟨x⟩ | ⟨x⟩ <;> rcases y with ⟨y⟩ | ⟨y⟩
  · -- x y : p
    by_cases h : x = y <;>
    simp [LieAlgebra.Orthogonal.Pso, LieAlgebra.Orthogonal.indefiniteDiagonal, h, one_apply]
  · -- x : p, y : q
    simp [LieAlgebra.Orthogonal.Pso, LieAlgebra.Orthogonal.indefiniteDiagonal]
  · -- x : q, y : p
    simp [LieAlgebra.Orthogonal.Pso, LieAlgebra.Orthogonal.indefiniteDiagonal]
  · -- x y : q
    by_cases h : x = y <;>
    simp [LieAlgebra.Orthogonal.Pso, LieAlgebra.Orthogonal.indefiniteDiagonal, h, hi, one_apply]

