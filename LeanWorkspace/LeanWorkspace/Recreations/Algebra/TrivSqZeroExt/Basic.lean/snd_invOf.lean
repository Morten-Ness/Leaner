import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

variable [AddCommGroup M] [Semiring R] [Module Rᵐᵒᵖ M] [Module R M]

variable [SMulCommClass R Rᵐᵒᵖ M]

theorem snd_invOf (x : tsze R M) [Invertible x] [Invertible x.fst] :
    (⅟x).snd = -(⅟x.fst •> x.snd <• ⅟x.fst) := by
  letI := invertibleOfInvertibleFst x
  convert congr_arg (TrivSqZeroExt.snd (R := R) (M := M)) (_ : _ = ⅟x)
  convert rfl

