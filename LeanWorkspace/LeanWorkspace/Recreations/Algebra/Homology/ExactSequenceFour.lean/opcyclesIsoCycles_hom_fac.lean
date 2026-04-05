import Mathlib

variable {C : Type*} [Category C] [Preadditive C] [Balanced C] {n : ℕ}
  {S : ComposableArrows C (n + 3)} (hS : S.Exact)

theorem opcyclesIsoCycles_hom_fac (k : ℕ) (hk : k ≤ n := by lia)
    [h₁ : (hS.sc k).HasRightHomology] [h₂ : (hS.sc (k + 1)).HasLeftHomology] :
    (hS.sc k _).pOpcycles ≫ (hS.opcyclesIsoCycles k).hom ≫ (hS.sc (k + 1) _).iCycles =
      S.map' (k + 1) (k + 2) :=
  CategoryTheory.ComposableArrows.IsComplex.opcyclesToCycles_fac hS.toIsComplex k hk

