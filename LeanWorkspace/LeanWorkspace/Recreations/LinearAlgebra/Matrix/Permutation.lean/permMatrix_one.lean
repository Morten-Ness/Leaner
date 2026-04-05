import Mathlib

variable {n R : Type*} [DecidableEq n] (σ τ : Perm n)

theorem permMatrix_one [Zero R] [One R] : (1 : Equiv.Perm n).permMatrix R = 1 := permMatrix_refl

