import Mathlib

variable {R N L M : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

set_option backward.isDefEq.respectTransparency false in
theorem ringModuleOf_bracket_proj [IsLieAbelian M] (E : LieAlgebra.Extension R M L) (y : M) (z : E.L) :
    letI := E.ringModuleOf
    ⁅E.proj z, y⁆ = E.toKer.symm ⁅z, E.toKer y⁆ := by
  obtain ⟨x, hx⟩ : E.proj_surjective.hasRightInverse.choose (E.proj z) - z ∈ E.incl.range := by
    rw [E.IsExtension.exact]
    change _ ∈ E.proj.ker
    simp [E.proj_surjective.hasRightInverse.choose_spec (E.proj z)]
  rw [ringModuleOf_bracket, EmbeddingLike.apply_eq_iff_eq, ← sub_eq_zero, ← sub_lie,
    Subtype.ext_iff, LieSubmodule.coe_bracket, lie_toKer_apply, ZeroMemClass.coe_zero, ← hx,
    LieHom.coe_toLinearMap, ← LieHom.map_lie, trivial_lie_zero M M x y, map_zero]

