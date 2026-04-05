import Mathlib

variable {R : Type*} [CommRing R] {a b : R}

theorem det_toLinearMap_eq_norm (z : QuadraticAlgebra R a b) :
    (DistribSMul.toLinearMap R (QuadraticAlgebra R a b) z).det = z.norm := by
  rw [← LinearMap.det_toMatrix <| basis ..]
  have : !![z.re, a * z.im; z.im, z.re + b * z.im].det = z.norm := by
    simp [norm]
    ring
  convert this
  apply LinearEquiv.eq_symm_apply _ |>.mp
  ext1 w
  apply basis .. |>.repr.injective
  apply DFunLike.coe_injective'
  rw [LinearMap.toMatrix_symm, Matrix.repr_toLin]
  ext i
  fin_cases i
    <;> simp
    <;> ring

