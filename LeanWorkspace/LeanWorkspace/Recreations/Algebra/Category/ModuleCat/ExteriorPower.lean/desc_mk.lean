import Mathlib

variable {R : Type u} [CommRing R]

theorem desc_mk {M : ModuleCat.{v} R} {n : ℕ} {N : ModuleCat.{max u v} R}
    (φ : M.AlternatingMap N n) (x : Fin n → M) :
    ModuleCat.exteriorPower.desc φ (ModuleCat.exteriorPower.mk x) = φ x := by
  apply ModuleCat.exteriorPower.alternatingMapLinearEquiv_apply_ιMulti

