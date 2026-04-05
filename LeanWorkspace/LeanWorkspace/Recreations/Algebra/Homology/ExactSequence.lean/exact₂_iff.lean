import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

variable {n : ℕ} (S : ComposableArrows C n)

theorem exact₂_iff (S : CategoryTheory.ComposableArrows C 2) (hS : S.IsComplex) :
    S.Exact ↔ (S.sc' hS 0 1 2).Exact := by
  constructor
  · intro h
    exact h.exact 0 (by lia)
  · intro h
    refine Exact.mk hS (fun i hi => ?_)
    obtain rfl : i = 0 := by lia
    exact h

