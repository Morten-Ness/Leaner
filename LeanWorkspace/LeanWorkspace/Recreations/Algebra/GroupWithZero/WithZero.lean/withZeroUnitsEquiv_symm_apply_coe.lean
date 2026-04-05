import Mathlib

variable {α β γ : Type*}

variable [Group α]

theorem withZeroUnitsEquiv_symm_apply_coe {G : Type*} [GroupWithZero G]
    [DecidablePred (fun a : G ↦ a = 0)] (a : Gˣ) :
    WithZero.withZeroUnitsEquiv.symm (a : G) = a := by
  simp

