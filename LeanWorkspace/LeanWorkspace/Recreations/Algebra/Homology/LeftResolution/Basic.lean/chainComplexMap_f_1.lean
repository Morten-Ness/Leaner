import Mathlib

variable {A C : Type*} [Category* C] [Category* A] (ι : C ⥤ A)

variable {ι} (Λ : LeftResolution ι) (X Y Z : A) (f : X ⟶ Y) (g : Y ⟶ Z)

variable [ι.Full] [ι.Faithful] [HasZeroMorphisms C] [Abelian A]

theorem chainComplexMap_f_1 :
    (Λ.chainComplexMap f).f 1 =
    (Λ.chainComplexXOneIso X).hom ≫
      Λ.F.map (kernel.map _ _ (ι.map (Λ.F.map f)) f (Λ.π.naturality f).symm) ≫
      (Λ.chainComplexXOneIso Y).inv := rfl

