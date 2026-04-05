import Mathlib

variable {A C : Type*} [Category* C] [Category* A] (ι : C ⥤ A)

variable {ι} (Λ : LeftResolution ι) (X Y Z : A) (f : X ⟶ Y) (g : Y ⟶ Z)

variable [ι.Full] [ι.Faithful] [HasZeroMorphisms C] [Abelian A]

set_option backward.isDefEq.respectTransparency false in
theorem exactAt_map_chainComplex_succ (n : ℕ) :
    ((ι.mapHomologicalComplex _).obj (Λ.chainComplex X)).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n
    (ComplexShape.prev_eq' _ (by dsimp; lia)) (by simp),
    ShortComplex.exact_iff_epi_kernel_lift]
  convert epi_comp (ι.map (Λ.chainComplexXIso X n).hom) (Λ.π.app _)
  rw [← cancel_mono (kernel.ι _), kernel.lift_ι]
  simp [CategoryTheory.Abelian.LeftResolution.map_chainComplex_d]

