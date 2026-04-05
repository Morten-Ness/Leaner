import Mathlib

open scoped Matrix

variable (n p q l : Type*) (R : Type u₂)

variable [DecidableEq n] [DecidableEq p] [DecidableEq q] [DecidableEq l]

variable [CommRing R]

theorem sl_non_abelian [Fintype n] [Nontrivial R] (h : 1 < Fintype.card n) :
    ¬IsLieAbelian (LieAlgebra.SpecialLinear.sl n R) := by
  rcases Fintype.exists_pair_of_one_lt_card h with ⟨i, j, hij⟩
  let A := LieAlgebra.SpecialLinear.single i j hij (1 : R)
  let B := LieAlgebra.SpecialLinear.single j i hij.symm (1 : R)
  intro c
  have c' : A.val * B.val = B.val * A.val := by
    rw [← sub_eq_zero, ← LieAlgebra.SpecialLinear.sl_bracket, c.trivial, ZeroMemClass.coe_zero]
  simpa [A, B, Matrix.single, Matrix.mul_apply, hij.symm] using congr_fun (congr_fun c' i) i

