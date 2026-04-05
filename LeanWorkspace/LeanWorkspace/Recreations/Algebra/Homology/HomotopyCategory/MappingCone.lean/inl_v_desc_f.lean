import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

variable {K : CochainComplex C ℤ}

variable (α : Cochain F K (-1)) (β : G ⟶ K) (eq : δ (-1) 0 α = Cochain.ofHom (φ ≫ β))

theorem inl_v_desc_f (p q : ℤ) (h : p + (-1) = q) :
    (CochainComplex.mappingCone.inl φ).v p q h ≫ (CochainComplex.mappingCone.desc φ α β eq).f q = α.v p q h := by
  simp [CochainComplex.mappingCone.desc]

