import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

variable {K : CochainComplex C ℤ}

variable (α : Cochain F K (-1)) (β : G ⟶ K) (eq : δ (-1) 0 α = Cochain.ofHom (φ ≫ β))

theorem inr_desc : CochainComplex.mappingCone.inr φ ≫ CochainComplex.mappingCone.desc φ α β eq = β := by cat_disch

