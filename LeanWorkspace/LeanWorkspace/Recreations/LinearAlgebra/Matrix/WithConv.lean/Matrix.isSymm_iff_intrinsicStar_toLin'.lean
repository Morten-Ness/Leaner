import Mathlib

variable {m n α β : Type*}

variable [CommSemiring α] [StarRing α] [Fintype n] [DecidableEq n]

theorem Matrix.isSymm_iff_intrinsicStar_toLin' {A : Matrix n n α} :
    A.IsSymm ↔ star (toConv A.toLin') = toConv (star A).toLin' := by
  rw [intrinsicStar_toLin', toConv_injective.eq_iff, toLin'.injective.eq_iff,
    ← transpose_conjTranspose, star_eq_conjTranspose, conjTranspose_inj, Matrix.IsSymm]

