import Mathlib

section

variable {R : Type u} [CommSemiring R]

theorem associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : SemimoduleCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (f₃ : X₃ ⟶ Y₃) :
    SemimoduleCat.MonoidalCategory.tensorHom (SemimoduleCat.MonoidalCategory.tensorHom f₁ f₂) f₃ ≫ (SemimoduleCat.MonoidalCategory.associator Y₁ Y₂ Y₃).hom =
      (SemimoduleCat.MonoidalCategory.associator X₁ X₂ X₃).hom ≫ SemimoduleCat.MonoidalCategory.tensorHom f₁ (SemimoduleCat.MonoidalCategory.tensorHom f₂ f₃) := by
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y z
  rfl

end

section

variable {R : Type u} [CommSemiring R]

theorem id_tensorHom_id (M N : SemimoduleCat R) :
    SemimoduleCat.MonoidalCategory.tensorHom (𝟙 M) (𝟙 N) = 𝟙 (SemimoduleCat.of R (M ⊗ N)) := by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): even with high priority `ext` fails to find this.
  apply TensorProduct.ext
  rfl

end

section

variable {R : Type u} [CommSemiring R]

theorem leftUnitor_naturality {M N : SemimoduleCat R} (f : M ⟶ N) :
    SemimoduleCat.MonoidalCategory.tensorHom (𝟙 (SemimoduleCat.of R R)) f ≫ (SemimoduleCat.MonoidalCategory.leftUnitor N).hom = (SemimoduleCat.MonoidalCategory.leftUnitor M).hom ≫ f := by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): broken ext
  apply TensorProduct.ext
  ext
  simp [SemimoduleCat.MonoidalCategory.tensorHom, SemimoduleCat.MonoidalCategory.tensorObj, SemimoduleCat.MonoidalCategory.leftUnitor]

end

section

variable {R : Type u} [CommSemiring R]

theorem pentagon (W X Y Z : SemimoduleCat R) :
    SemimoduleCat.MonoidalCategory.whiskerRight (SemimoduleCat.MonoidalCategory.associator W X Y).hom Z ≫
        (SemimoduleCat.MonoidalCategory.associator W (SemimoduleCat.MonoidalCategory.tensorObj X Y) Z).hom ≫ SemimoduleCat.MonoidalCategory.whiskerLeft W (SemimoduleCat.MonoidalCategory.associator X Y Z).hom =
      (SemimoduleCat.MonoidalCategory.associator (SemimoduleCat.MonoidalCategory.tensorObj W X) Y Z).hom ≫ (SemimoduleCat.MonoidalCategory.associator W X (SemimoduleCat.MonoidalCategory.tensorObj Y Z)).hom := by
  ext : 1
  apply TensorProduct.ext_fourfold
  intro w x y z
  rfl

end

section

variable {R : Type u} [CommSemiring R]

theorem rightUnitor_naturality {M N : SemimoduleCat R} (f : M ⟶ N) :
    SemimoduleCat.MonoidalCategory.tensorHom f (𝟙 (SemimoduleCat.of R R)) ≫ (SemimoduleCat.MonoidalCategory.rightUnitor N).hom = (SemimoduleCat.MonoidalCategory.rightUnitor M).hom ≫ f := by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): broken ext
  apply TensorProduct.ext
  ext
  simp [SemimoduleCat.MonoidalCategory.tensorHom, SemimoduleCat.MonoidalCategory.tensorObj, SemimoduleCat.MonoidalCategory.rightUnitor]

end

section

variable {R : Type u} [CommSemiring R]

theorem tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : SemimoduleCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    SemimoduleCat.MonoidalCategory.tensorHom f₁ f₂ ≫ SemimoduleCat.MonoidalCategory.tensorHom g₁ g₂ = SemimoduleCat.MonoidalCategory.tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) := by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): even with high priority `ext` fails to find this.
  apply TensorProduct.ext
  rfl

end

section

variable {R : Type u} [CommSemiring R]

theorem triangle (M N : SemimoduleCat.{u} R) :
    (SemimoduleCat.MonoidalCategory.associator M (SemimoduleCat.of R R) N).hom ≫ SemimoduleCat.MonoidalCategory.tensorHom (𝟙 M) (SemimoduleCat.MonoidalCategory.leftUnitor N).hom =
      SemimoduleCat.MonoidalCategory.tensorHom (SemimoduleCat.MonoidalCategory.rightUnitor M).hom (𝟙 N) := by
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y
  exact TensorProduct.tmul_smul _ _

end
