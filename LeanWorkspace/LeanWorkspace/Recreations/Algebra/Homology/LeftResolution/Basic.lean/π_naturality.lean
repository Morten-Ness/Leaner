import Mathlib

variable {A C : Type*} [Category* C] [Category* A] (ι : C ⥤ A)

variable {ι} (Λ : LeftResolution ι) (X Y Z : A) (f : X ⟶ Y) (g : Y ⟶ Z)

theorem π_naturality : ι.map (Λ.F.map f) ≫ Λ.π.app Y = Λ.π.app X ≫ f := Λ.π.naturality f

