import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

theorem _root_.HomotopyEquiv.isKProjective {K₁ K₂ : CochainComplex C ℤ}
    (e : HomotopyEquiv K₁ K₂)
    [K₁.IsKProjective] : K₂.IsKProjective where
  nonempty_homotopy_zero {L} f hL := ⟨Homotopy.trans (Homotopy.trans (.ofEq (by simp))
      ((e.homotopyInvHomId.symm.compRight f).trans (.ofEq (by simp))))
        (((IsKProjective.homotopyZero (e.hom ≫ f) hL).compLeft e.inv).trans (.ofEq (by simp)))⟩

