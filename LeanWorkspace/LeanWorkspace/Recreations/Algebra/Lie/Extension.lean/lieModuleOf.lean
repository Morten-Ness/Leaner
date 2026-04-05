import Mathlib

variable {R N L M : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

set_option backward.isDefEq.respectTransparency false in
theorem lieModuleOf [IsLieAbelian M] (E : LieAlgebra.Extension R M L) :
    letI := E.ringModuleOf
    LieModule R L M := by
  letI := E.ringModuleOf
  set h := E.proj_surjective.hasRightInverse
  exact
    { smul_lie r x m := by
        rw [ringModuleOf_bracket, ringModuleOf_bracket, ← map_smul, ← smul_lie,
          EquivLike.apply_eq_iff_eq, ← sub_eq_zero, ← sub_lie]
        exact trivial_lie_zero E.proj.ker _ ⟨_, by simp [h.choose_spec _]⟩ (E.toKer m)
      lie_smul r x m := by simp }

