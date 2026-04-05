import Mathlib

variable {R N L M : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

set_option backward.isDefEq.respectTransparency false in
theorem lie_apply_proj_of_leftInverse_eq [IsLieAbelian M] (E : LieAlgebra.Extension R M L) {s : L →ₗ[R] E.L}
    (hs : LeftInverse E.proj s) (x : E.L) (y : E.proj.ker) :
    ⁅s (E.proj x), y⁆ = ⁅x, y⁆ := by
  rw [← sub_eq_zero, ← sub_lie]
  exact trivial_lie_zero E.proj.ker E.proj.ker ⟨_, (by simp [hs.eq])⟩ y

