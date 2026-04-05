import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

theorem span_eq : span R (Set.range b) = ⊤ := eq_top_iff.mpr fun x _ => Module.Basis.mem_span b x

