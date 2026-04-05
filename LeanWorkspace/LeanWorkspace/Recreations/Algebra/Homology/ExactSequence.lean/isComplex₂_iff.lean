import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

variable {n : ℕ} (S : ComposableArrows C n)

theorem isComplex₂_iff (S : CategoryTheory.ComposableArrows C 2) :
    S.IsComplex ↔ S.map' 0 1 ≫ S.map' 1 2 = 0 := by
  constructor
  · intro h
    exact h.zero 0 (by lia)
  · intro h
    refine IsComplex.mk (fun i hi => ?_)
    obtain rfl : i = 0 := by lia
    exact h

