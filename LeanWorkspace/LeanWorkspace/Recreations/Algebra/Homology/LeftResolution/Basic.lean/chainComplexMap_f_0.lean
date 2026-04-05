import Mathlib

variable {A C : Type*} [Category* C] [Category* A] (ι : C ⥤ A)

variable {ι} (Λ : LeftResolution ι) (X Y Z : A) (f : X ⟶ Y) (g : Y ⟶ Z)

variable [ι.Full] [ι.Faithful] [HasZeroMorphisms C] [Abelian A]

theorem chainComplexMap_f_0 :
    (Λ.chainComplexMap f).f 0 =
      ((Λ.chainComplexXZeroIso X).hom ≫ Λ.F.map f ≫ (Λ.chainComplexXZeroIso Y).inv) := rfl

