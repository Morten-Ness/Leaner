import Mathlib

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem fst_comp_inl [DecidablePred fun x : G₀ ↦ x = 0] :
    (MonoidWithZeroHom.fst ..).comp (MonoidWithZeroHom.inl G₀ H₀) = .id _ := MonoidWithZeroHom.ext fun _ ↦ MonoidWithZeroHom.fst_inl _

