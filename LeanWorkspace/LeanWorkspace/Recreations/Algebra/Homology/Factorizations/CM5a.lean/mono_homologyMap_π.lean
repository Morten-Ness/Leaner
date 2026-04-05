import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

variable {K L : CochainComplex C ℤ} (f : K ⟶ L)

variable [EnoughInjectives C] (n : ℤ)

theorem mono_homologyMap_π (q : ℤ) (hq : q ≤ n) : Mono (homologyMap (π f n) q) := (CochainComplex.homologyMap_exact₁_of_distTriang _
    (DerivedCategory.mappingCocone_triangle_distinguished (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₂.α f n)) (q - 1) q (by lia)).mono_g
      ((ExactAt.isZero_homology (exactAt_single_obj _ _ _ _ (by lia))).eq_of_src _ _)

