import Mathlib

theorem vec_single [DecidableEq m] [DecidableEq n] [Zero R] (i : m) (j : n) (r : R) :
    Matrix.vec (Matrix.single i j r) = Pi.single (j, i) r := by
  rw [single_eq_of_single_single, Matrix.vec_of, Function.uncurry_flip, Pi.uncurry_single_single]
  exact Pi.single_comp_equiv (Equiv.prodComm _ _) _ _

