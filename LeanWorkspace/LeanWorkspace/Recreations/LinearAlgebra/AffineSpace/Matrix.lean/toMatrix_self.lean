import Mathlib

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P)

theorem toMatrix_self [DecidableEq ι] : b.toMatrix b = (1 : Matrix ι ι k) := by
  ext i j
  rw [AffineBasis.toMatrix_apply, coord_apply, Matrix.one_eq_pi_single, Pi.single_apply]

