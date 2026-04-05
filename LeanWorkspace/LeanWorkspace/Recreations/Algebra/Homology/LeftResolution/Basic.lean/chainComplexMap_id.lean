import Mathlib

variable {A C : Type*} [Category* C] [Category* A] (ι : C ⥤ A)

variable {ι} (Λ : LeftResolution ι) (X Y Z : A) (f : X ⟶ Y) (g : Y ⟶ Z)

variable [ι.Full] [ι.Faithful] [HasZeroMorphisms C] [Abelian A]

theorem chainComplexMap_id : Λ.chainComplexMap (𝟙 X) = 𝟙 _ := by
  ext n
  induction n with
  | zero => simp
  | succ n hn => obtain _ | n := n <;> simp [hn]

