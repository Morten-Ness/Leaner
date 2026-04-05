import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
  {i'' j'' k'' : ι} (f'' : i'' ⟶ j'') (g'' : j'' ⟶ k'')

variable (fg : i ⟶ k) (h : f ≫ g = fg) (fg' : i' ⟶ k') (h' : f' ≫ g' = fg')

theorem isIso_fromOpcycles (n : ℤ) (hg : IsZero ((X.H n).obj (mk₁ g))) :
    IsIso (X.fromOpcycles f g fg h n) := by
  have : Epi (X.fromOpcycles f g fg h n) :=
    (X.kernelSequenceOpcycles_exact f g fg h n).epi_f (hg.eq_of_tgt _ _)
  exact Balanced.isIso_of_mono_of_epi _

