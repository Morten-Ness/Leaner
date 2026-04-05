import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem inf_toSubalgebra (S T : StarSubalgebra R A) :
    (S ⊓ T).toSubalgebra = S.toSubalgebra ⊓ T.toSubalgebra := by
  ext; simp
-- Porting note: Lean can no longer prove this by `rfl`, it times out

