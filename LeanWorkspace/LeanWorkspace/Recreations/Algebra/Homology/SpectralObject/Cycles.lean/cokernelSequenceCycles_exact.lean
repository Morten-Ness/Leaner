import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
  {i'' j'' k'' : ι} (f'' : i'' ⟶ j'') (g'' : j'' ⟶ k'')

variable (fg : i ⟶ k) (h : f ≫ g = fg) (fg' : i' ⟶ k') (h' : f' ≫ g' = fg')

set_option backward.isDefEq.respectTransparency false in
theorem cokernelSequenceCycles_exact (n : ℤ) :
    (X.cokernelSequenceCycles f g fg h n).Exact := by
  apply ShortComplex.exact_of_g_is_cokernel
  exact IsColimit.ofIsoColimit (cokernelIsCokernel _)
    (Cofork.ext (X.cokernelIsoCycles f g fg h n) (by
      simp [← cancel_mono (X.iCycles f g n)]))

