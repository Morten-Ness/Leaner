import Mathlib

section

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {W : Type*} [Category* W] [Preadditive W]

variable {W₁ W₂ : Type*} [Category* W₁] [Category* W₂] [HasZeroMorphisms W₁] [HasZeroMorphisms W₂]

variable {c : ComplexShape ι} {C D : HomologicalComplex V c}

variable (f : C ⟶ D) (i : ι)

variable {α : Type*} [AddRightCancelSemigroup α] [One α] [DecidableEq α]

set_option backward.isDefEq.respectTransparency false in
theorem map_chain_complex_of (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms] (X : α → W₁)
    (d : ∀ n, X (n + 1) ⟶ X n) (sq : ∀ n, d (n + 1) ≫ d n = 0) :
    (F.mapHomologicalComplex _).obj (ChainComplex.of X d sq) =
      ChainComplex.of (fun n => F.obj (X n)) (fun n => F.map (d n)) fun n => by
        rw [← F.map_comp, sq n, Functor.map_zero] := by
  refine HomologicalComplex.ext rfl ?_
  rintro i j (rfl : j + 1 = i)
  simp only [CategoryTheory.Functor.mapHomologicalComplex_obj_d, of_d, eqToHom_refl, comp_id,
    id_comp]

end

section

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {W : Type*} [Category* W] [Preadditive W]

variable {W₁ W₂ : Type*} [Category* W₁] [Category* W₂] [HasZeroMorphisms W₁] [HasZeroMorphisms W₂]

variable {c : ComplexShape ι} {C D : HomologicalComplex V c}

variable (f : C ⟶ D) (i : ι)

variable [HasZeroObject W₁] [HasZeroObject W₂]

variable (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms]
    (c : ComplexShape ι) [DecidableEq ι]

theorem singleMapHomologicalComplex_hom_app_ne {i j : ι} (h : i ≠ j) (X : W₁) :
    ((HomologicalComplex.singleMapHomologicalComplex F c j).hom.app X).f i = 0 := by
  simp [HomologicalComplex.singleMapHomologicalComplex, h]

end

section

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {W : Type*} [Category* W] [Preadditive W]

variable {W₁ W₂ : Type*} [Category* W₁] [Category* W₂] [HasZeroMorphisms W₁] [HasZeroMorphisms W₂]

variable {c : ComplexShape ι} {C D : HomologicalComplex V c}

variable (f : C ⟶ D) (i : ι)

variable [HasZeroObject W₁] [HasZeroObject W₂]

variable (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms]
    (c : ComplexShape ι) [DecidableEq ι]

theorem singleMapHomologicalComplex_hom_app_self (j : ι) (X : W₁) :
    ((HomologicalComplex.singleMapHomologicalComplex F c j).hom.app X).f j =
      F.map (singleObjXSelf c j X).hom ≫ (singleObjXSelf c j (F.obj X)).inv := by
  simp [HomologicalComplex.singleMapHomologicalComplex, singleObjXSelf, singleObjXIsoOfEq, eqToHom_map]

end

section

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {W : Type*} [Category* W] [Preadditive W]

variable {W₁ W₂ : Type*} [Category* W₁] [Category* W₂] [HasZeroMorphisms W₁] [HasZeroMorphisms W₂]

variable {c : ComplexShape ι} {C D : HomologicalComplex V c}

variable (f : C ⟶ D) (i : ι)

variable [HasZeroObject W₁] [HasZeroObject W₂]

variable (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms]
    (c : ComplexShape ι) [DecidableEq ι]

theorem singleMapHomologicalComplex_inv_app_ne {i j : ι} (h : i ≠ j) (X : W₁) :
    ((HomologicalComplex.singleMapHomologicalComplex F c j).inv.app X).f i = 0 := by
  simp [HomologicalComplex.singleMapHomologicalComplex, h]

end

section

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {W : Type*} [Category* W] [Preadditive W]

variable {W₁ W₂ : Type*} [Category* W₁] [Category* W₂] [HasZeroMorphisms W₁] [HasZeroMorphisms W₂]

variable {c : ComplexShape ι} {C D : HomologicalComplex V c}

variable (f : C ⟶ D) (i : ι)

variable [HasZeroObject W₁] [HasZeroObject W₂]

variable (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms]
    (c : ComplexShape ι) [DecidableEq ι]

theorem singleMapHomologicalComplex_inv_app_self (j : ι) (X : W₁) :
    ((HomologicalComplex.singleMapHomologicalComplex F c j).inv.app X).f j =
      (singleObjXSelf c j (F.obj X)).hom ≫ F.map (singleObjXSelf c j X).inv := by
  simp [HomologicalComplex.singleMapHomologicalComplex, singleObjXSelf, singleObjXIsoOfEq, eqToHom_map]

end
