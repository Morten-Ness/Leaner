import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
  {i'' j'' k'' : ι} (f'' : i'' ⟶ j'') (g'' : j'' ⟶ k'')

variable (fg : i ⟶ k) (h : f ≫ g = fg) (fg' : i' ⟶ k') (h' : f' ≫ g' = fg')

theorem isIso_toCycles (n : ℤ) (hf : IsZero ((X.H n).obj (mk₁ f))) :
    IsIso (X.toCycles f g fg h n) := by
  have : Mono (X.toCycles f g fg h n) :=
    (X.cokernelSequenceCycles_exact f g fg h n).mono_g (hf.eq_of_src _ _)
  exact Balanced.isIso_of_mono_of_epi _

