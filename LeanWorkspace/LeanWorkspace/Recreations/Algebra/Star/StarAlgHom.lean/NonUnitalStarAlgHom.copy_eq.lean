import Mathlib

variable {R A B C D : Type*} [Monoid R]

variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]

variable [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]

variable [NonUnitalNonAssocSemiring C] [DistribMulAction R C] [Star C]

variable [NonUnitalNonAssocSemiring D] [DistribMulAction R D] [Star D]

theorem copy_eq (f : A →⋆ₙₐ[R] B) (f' : A → B) (h : f' = f) : f.copy f' h = f := DFunLike.ext' h

#adaptation_note /-- After https://github.com/leanprover/lean4/pull/12179
the simpNF linter complains about this being `@[simp]`. -/

