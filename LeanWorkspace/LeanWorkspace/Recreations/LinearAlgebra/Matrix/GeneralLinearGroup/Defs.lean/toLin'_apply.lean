import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v}

variable [CommRing R]

theorem toLin'_apply {V : Type*} [AddCommGroup V] [Module R V]
    (b : Module.Basis n R V) (M : GL n R) (v : V) :
    (Matrix.GeneralLinearGroup.toLin' b M).toLinearEquiv v = Fintype.linearCombination R ⇑b (↑M *ᵥ (b.repr v)) := by
  simp [Matrix.GeneralLinearGroup.toLin', Matrix.GeneralLinearGroup.toLin, Fintype.linearCombination_apply, MulEquiv.trans_apply]

