import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem left_fac_of_isStrictlyLE_of_isStrictlyGE
    {X Y : CochainComplex C ℤ} (a b : ℤ)
    [X.IsStrictlyLE b] [Y.IsStrictlyGE a] [Y.IsStrictlyLE b] (f : Q.obj X ⟶ Q.obj Y) :
    ∃ (Y' : CochainComplex C ℤ) (_ : Y'.IsStrictlyGE a) (_ : Y'.IsStrictlyLE b)
    (g : X ⟶ Y') (s : Y ⟶ Y') (_ : IsIso (Q.map s)), f = Q.map g ≫ inv (Q.map s) := by
  obtain ⟨Y', hY', g, s, hs, fac⟩ := DerivedCategory.left_fac_of_isStrictlyGE f a
  have : IsIso (Q.map (CochainComplex.truncLEMap s b)) := by
    rw [isIso_Q_map_iff_quasiIso] at hs
    rw [isIso_Q_map_iff_quasiIso, CochainComplex.quasiIso_truncLEMap_iff]
    infer_instance
  refine ⟨Y'.truncLE b, inferInstance, inferInstance,
    inv (X.ιTruncLE b) ≫ CochainComplex.truncLEMap g b,
    inv (Y.ιTruncLE b) ≫ CochainComplex.truncLEMap s b, ?_, ?_⟩
  · rw [Q.map_comp]
    infer_instance
  · simp only [Functor.map_comp, Functor.map_inv, IsIso.inv_comp, IsIso.inv_inv, assoc, fac,
      ← cancel_mono (Q.map s), IsIso.inv_hom_id, comp_id]
    rw [← Functor.map_comp, ← CochainComplex.ιTruncLE_naturality s b,
      Functor.map_comp, IsIso.inv_hom_id_assoc,
      ← Functor.map_comp, CochainComplex.ιTruncLE_naturality g b,
      Functor.map_comp, IsIso.inv_hom_id_assoc]

