import Mathlib

variable {C : Type*} [Category C] [HasZeroMorphisms C] {n : ℕ} {S : ComposableArrows C (n + 3)}
  (hS : S.IsComplex) (k : ℕ)

theorem opcyclesToCycles_fac (hk : k ≤ n := by lia)
    [(S.sc hS k).HasRightHomology] [(S.sc hS (k + 1)).HasLeftHomology] :
    (S.sc hS k _).pOpcycles ≫ hS.opcyclesToCycles k ≫ (S.sc hS (k + 1) _).iCycles =
      S.map' (k + 1) (k + 2) :=
  CategoryTheory.ComposableArrows.IsComplex.cokerToKer'_fac hS k hk _ _ (S.sc hS k _).opcyclesIsCokernel
    (S.sc hS (k + 1) _).cyclesIsKernel

