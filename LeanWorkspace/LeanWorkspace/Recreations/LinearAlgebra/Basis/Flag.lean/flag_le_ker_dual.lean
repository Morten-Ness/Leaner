import Mathlib

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}

theorem flag_le_ker_dual (b : Module.Basis (Fin n) R M) (k : Fin n) :
    b.flag k.castSucc ≤ LinearMap.ker (b.dualBasis k) := by
  nontriviality R
  rw [coe_dualBasis, Module.Basis.flag_le_ker_coord_iff b]

