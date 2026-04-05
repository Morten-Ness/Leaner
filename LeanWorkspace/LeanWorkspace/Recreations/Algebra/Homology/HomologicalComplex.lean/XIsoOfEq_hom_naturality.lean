import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

theorem XIsoOfEq_hom_naturality {K L : HomologicalComplex V c} (φ : K ⟶ L) {n n' : ι} (h : n = n') :
    φ.f n ≫ (L.XIsoOfEq h).hom = (K.XIsoOfEq h).hom ≫ φ.f n' := by subst h; simp

