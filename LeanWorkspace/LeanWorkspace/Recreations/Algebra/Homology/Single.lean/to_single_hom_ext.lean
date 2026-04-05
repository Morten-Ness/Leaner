import Mathlib

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

variable {ι : Type*} [DecidableEq ι] (c : ComplexShape ι)

theorem to_single_hom_ext {K : HomologicalComplex V c} {j : ι} {A : V}
    {f g : K ⟶ (HomologicalComplex.single V c j).obj A} (hfg : f.f j = g.f j) : f = g := by
  ext i
  by_cases h : i = j
  · subst h
    exact hfg
  · apply (HomologicalComplex.isZero_single_obj_X c j A i h).eq_of_tgt

