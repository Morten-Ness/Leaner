FAIL
import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v} [dec_ι : DecidableEq ι]

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable (A : ι → Submodule R M)

set_option backward.isDefEq.respectTransparency false in
theorem coeLinearMap_eq_dfinsuppSum [DecidableEq M] (x : DirectSum ι fun i => A i) :
    DirectSum.coeLinearMap A x = DFinsupp.sum x fun i => (fun x : A i => ↑x) := by
  classical
  rw [DirectSum.coeLinearMap]
  exact DFinsupp.sum_apply _ _ x
