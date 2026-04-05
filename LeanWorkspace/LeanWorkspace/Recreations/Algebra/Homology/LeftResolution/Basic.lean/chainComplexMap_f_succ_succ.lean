import Mathlib

variable {A C : Type*} [Category* C] [Category* A] (ι : C ⥤ A)

variable {ι} (Λ : LeftResolution ι) (X Y Z : A) (f : X ⟶ Y) (g : Y ⟶ Z)

variable [ι.Full] [ι.Faithful] [HasZeroMorphisms C] [Abelian A]

theorem chainComplexMap_f_succ_succ (n : ℕ) :
    (Λ.chainComplexMap f).f (n + 2) =
      (Λ.chainComplexXIso X n).hom ≫
        Λ.F.map (kernel.map _ _ (ι.map ((Λ.chainComplexMap f).f (n + 1)))
          (ι.map ((Λ.chainComplexMap f).f n))
          (by rw [← ι.map_comp, ← ι.map_comp, HomologicalComplex.Hom.comm])) ≫
          (Λ.chainComplexXIso Y n).inv := by
  apply ChainComplex.mkHom_f_succ_succ

