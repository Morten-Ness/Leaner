import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

variable {K L : CochainComplex C ℤ} (f : K ⟶ L)

variable [EnoughInjectives C] (n : ℤ)

theorem epi_homologyMap_π (q : ℤ) (hq : q < n) : Epi (homologyMap (π f n) q) := (CochainComplex.homologyMap_exact₂_of_distTriang _
    (DerivedCategory.mappingCocone_triangle_distinguished (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₂.α f n)) q).epi_f
      ((ExactAt.isZero_homology (exactAt_single_obj _ _ _ _ (by lia))).eq_of_tgt _ _)

