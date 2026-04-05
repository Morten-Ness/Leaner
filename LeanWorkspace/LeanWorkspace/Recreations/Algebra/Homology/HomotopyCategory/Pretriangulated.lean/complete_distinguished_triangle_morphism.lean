import Mathlib

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasBinaryBiproducts C]
  [Preadditive D] [HasBinaryBiproducts D]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

set_option backward.isDefEq.respectTransparency false in
theorem complete_distinguished_triangle_morphism
    (T₁ T₂ : Triangle (HomotopyCategory C (ComplexShape.up ℤ)))
    (hT₁ : T₁ ∈ HomotopyCategory.Pretriangulated.distinguishedTriangles C) (hT₂ : T₂ ∈ HomotopyCategory.Pretriangulated.distinguishedTriangles C)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (fac : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ (c : T₁.obj₃ ⟶ T₂.obj₃), T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
      T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := by
  obtain ⟨K₁, L₁, φ₁, ⟨e₁⟩⟩ := hT₁
  obtain ⟨K₂, L₂, φ₂, ⟨e₂⟩⟩ := hT₂
  obtain ⟨a', ha'⟩ : ∃ (a' : (quotient _ _).obj K₁ ⟶ (quotient _ _).obj K₂),
    a' = e₁.inv.hom₁ ≫ a ≫ e₂.hom.hom₁ := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ (b' : (quotient _ _).obj L₁ ⟶ (quotient _ _).obj L₂),
    b' = e₁.inv.hom₂ ≫ b ≫ e₂.hom.hom₂ := ⟨_, rfl⟩
  obtain ⟨a'', rfl⟩ := (quotient _ _).map_surjective a'
  obtain ⟨b'', rfl⟩ := (quotient _ _).map_surjective b'
  have H : Homotopy (φ₁ ≫ b'') (a'' ≫ φ₂) := homotopyOfEq _ _ (by
    have comm₁₁ := e₁.inv.comm₁
    have comm₁₂ := e₂.hom.comm₁
    dsimp at comm₁₁ comm₁₂
    simp only [Functor.map_comp, ha', hb', reassoc_of% comm₁₁,
      reassoc_of% fac, comm₁₂, assoc])
  let γ := e₁.hom ≫ CochainComplex.mappingCone.trianglehMapOfHomotopy H ≫ e₂.inv
  have comm₂ := γ.comm₂
  have comm₃ := γ.comm₃
  dsimp [γ] at comm₂ comm₃
  simp only [ha', hb'] at comm₂ comm₃
  refine ⟨γ.hom₃, ?_, ?_⟩
  -- the following list of lemmas was obtained by doing simpa? [γ] using comm₂
  · simpa only [triangleCategory_comp, Functor.mapTriangle_obj, triangle_obj₁, triangle_obj₂,
      triangle_obj₃, triangle_mor₁, triangle_mor₂, TriangleMorphism.comp_hom₃, Triangle.mk_obj₃,
      trianglehMapOfHomotopy_hom₃, TriangleMorphism.comm₂_assoc, Triangle.mk_obj₂,
      Triangle.mk_mor₂, assoc, Iso.hom_inv_id_triangle_hom₂, comp_id,
      Iso.hom_inv_id_triangle_hom₂_assoc, γ] using comm₂
  -- the following list of lemmas was obtained by doing simpa? [γ] using comm₃
  · simpa only [triangleCategory_comp, Functor.mapTriangle_obj, triangle_obj₁, triangle_obj₂,
      triangle_obj₃, triangle_mor₁, triangle_mor₂, TriangleMorphism.comp_hom₃, Triangle.mk_obj₃,
      trianglehMapOfHomotopy_hom₃, assoc, Triangle.mk_obj₁, Iso.hom_inv_id_triangle_hom₁, comp_id,
      Iso.hom_inv_id_triangle_hom₁_assoc, γ] using comm₃

