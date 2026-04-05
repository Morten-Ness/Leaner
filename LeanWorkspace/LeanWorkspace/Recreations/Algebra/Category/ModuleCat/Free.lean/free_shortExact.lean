import Mathlib

variable {ι ι' R : Type*} [Ring R] {S : ShortComplex (ModuleCat R)}
  (hS : S.Exact) (hS' : S.ShortExact) {v : ι → S.X₁}

theorem free_shortExact [Module.Free R S.X₁] [Module.Free R S.X₃] :
    Module.Free R S.X₂ := Module.Free.of_basis (ModuleCat.Basis.ofShortExact hS' (Module.Free.chooseBasis R S.X₁)
    (Module.Free.chooseBasis R S.X₃))

