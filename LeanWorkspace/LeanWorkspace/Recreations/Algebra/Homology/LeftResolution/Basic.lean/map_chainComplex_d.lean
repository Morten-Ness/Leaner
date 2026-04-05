import Mathlib

variable {A C : Type*} [Category* C] [Category* A] (ι : C ⥤ A)

variable {ι} (Λ : LeftResolution ι) (X Y Z : A) (f : X ⟶ Y) (g : Y ⟶ Z)

variable [ι.Full] [ι.Faithful] [HasZeroMorphisms C] [Abelian A]

set_option backward.isDefEq.respectTransparency false in
theorem map_chainComplex_d (n : ℕ) :
    ι.map ((Λ.chainComplex X).d (n + 2) (n + 1)) =
    ι.map (Λ.chainComplexXIso X n).hom ≫ Λ.π.app (kernel (ι.map ((Λ.chainComplex X).d (n + 1) n))) ≫
      kernel.ι (ι.map ((Λ.chainComplex X).d (n + 1) n)) := by
  have := ι.map_preimage (Λ.π.app _ ≫ kernel.ι (ι.map ((Λ.chainComplex X).d (n + 1) n)))
  dsimp at this
  rw [← this, ← Functor.map_comp]
  congr 1
  apply ChainComplex.mk'_d

attribute [irreducible] CategoryTheory.Abelian.LeftResolution.chainComplex

