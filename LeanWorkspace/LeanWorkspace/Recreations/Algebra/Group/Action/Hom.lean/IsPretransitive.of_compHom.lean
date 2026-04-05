import Mathlib

variable {M N α : Type*}

variable [Monoid M] [MulAction M α]

theorem IsPretransitive.of_compHom {M N α : Type*} [Monoid M] [Monoid N] [MulAction N α]
    (f : M →* N) [h : letI := compHom α f; IsPretransitive M α] : IsPretransitive N α :=
  letI := compHom α f; h.of_smul_eq f rfl

