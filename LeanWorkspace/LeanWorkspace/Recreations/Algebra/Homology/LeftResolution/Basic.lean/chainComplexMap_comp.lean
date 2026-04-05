import Mathlib

variable {A C : Type*} [Category* C] [Category* A] (ι : C ⥤ A)

variable {ι} (Λ : LeftResolution ι) (X Y Z : A) (f : X ⟶ Y) (g : Y ⟶ Z)

variable [ι.Full] [ι.Faithful] [HasZeroMorphisms C] [Abelian A]

theorem chainComplexMap_comp :
    Λ.chainComplexMap (f ≫ g) = Λ.chainComplexMap f ≫ Λ.chainComplexMap g := by
  ext n
  induction n with
  | zero => simp
  | succ n hn =>
    obtain _ | n := n
    all_goals
      dsimp
      simp only [CategoryTheory.Abelian.LeftResolution.chainComplexMap_f_succ_succ, assoc, Iso.cancel_iso_hom_left,
        Iso.inv_hom_id_assoc, ← Λ.F.map_comp_assoc, Iso.cancel_iso_inv_right_assoc]
      congr 1
      cat_disch

