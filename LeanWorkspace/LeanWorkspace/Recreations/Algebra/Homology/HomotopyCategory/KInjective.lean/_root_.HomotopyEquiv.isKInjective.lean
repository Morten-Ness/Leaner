import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

theorem _root_.HomotopyEquiv.isKInjective {L₁ L₂ : CochainComplex C ℤ}
    (e : HomotopyEquiv L₁ L₂)
    [L₁.IsKInjective] : L₂.IsKInjective where
  nonempty_homotopy_zero {K} f hK := ⟨Homotopy.trans (Homotopy.trans (.ofEq (by simp))
      ((e.homotopyInvHomId.symm.compLeft f).trans (.ofEq (by simp))))
        (((IsKInjective.homotopyZero (f ≫ e.inv) hK).compRight e.hom).trans (.ofEq (by simp)))⟩

