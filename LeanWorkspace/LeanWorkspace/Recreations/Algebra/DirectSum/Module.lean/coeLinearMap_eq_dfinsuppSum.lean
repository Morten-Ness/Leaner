import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v} [dec_ι : DecidableEq ι]

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable (A : ι → Submodule R M)

set_option backward.isDefEq.respectTransparency false in
theorem coeLinearMap_eq_dfinsuppSum [DecidableEq M] (x : DirectSum ι fun i => A i) :
    DirectSum.coeLinearMap A x = DFinsupp.sum x fun i => (fun x : A i => ↑x) := by
  simp only [DirectSum.coeLinearMap, DirectSum.toModule, DFinsupp.lsum, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [DFinsupp.sumAddHom_apply]
  simp only [LinearMap.toAddMonoidHom_coe, Submodule.coe_subtype]

