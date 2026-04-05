import Mathlib

variable {R N L M : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

set_option backward.isDefEq.respectTransparency false in
theorem d₁₂_oneCochainOfTwoSplitting [IsLieAbelian M] (E : LieAlgebra.Extension R M L) {s₁ s₂ : L →ₗ[R] E.L}
    (hs₁ : LeftInverse E.proj s₁) (hs₂ : LeftInverse E.proj s₂) :
    letI := E.ringModuleOf
    letI := E.lieModuleOf
    d₁₂ R L M (E.oneCochainOfTwoSplitting hs₁ hs₂) = E.twoCocycleOf hs₁ - E.twoCocycleOf hs₂ := by
  ext x y
  choose s hs using E.proj_surjective
  have {s' : L → E.L} (h : LeftInverse E.proj s') : ⁅s x - s' x, s' y - s y⁆ = (0 : E.L) := by
    have aux := trivial_lie_zero E.proj.ker E.proj.ker
      ⟨s x - s' x, by rw [LieHom.mem_ker, map_sub, sub_eq_zero, h, hs]⟩
      ⟨s' y - s y, by rw [LieHom.mem_ker, map_sub, sub_eq_zero, h, hs]⟩
    simpa only [Subtype.ext_iff, LieSubmodule.coe_zero, LieIdeal.coe_bracket_of_module,
      LieSubmodule.coe_bracket] using aux
  replace this {s' : L → E.L} (h : LeftInverse E.proj s') :
      ⁅s x, s' y⁆ = ⁅s' x, s' y⁆ + (⁅s x, s y⁆ - ⁅s' x, s y⁆) := by
    simpa [sub_sub, sub_eq_zero] using this h
  simp only [d₁₂_apply_coe_apply_apply, oneCochainOfTwoSplitting_apply, AddSubgroupClass.coe_sub,
    twoCocycleOf_coe_coe, LinearMap.sub_apply, LinearMap.compr₂_apply, LinearMap.coe_mk,
    AddHom.coe_mk, LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv]
  nth_rw 1 [← hs x]
  nth_rw 4 [← hs y]
  simp only [← EmbeddingLike.apply_eq_iff_eq E.toKer, LieAlgebra.Extension.ringModuleOf_bracket_proj,
    LieEquiv.apply_symm_apply, map_sub, Subtype.ext_iff, AddSubgroupClass.coe_sub,
    LieSubmodule.coe_bracket, lie_sub, this hs₁, this hs₂, ← lie_skew (s₁ x) (s y),
    ← lie_skew (s₂ x) (s y)]
  abel

