import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable {v : ι → M} {x y : M}

variable (hli : LinearIndependent R v)

theorem span_apply (i : ι) :
    Module.Basis.span hli i = ⟨v i, Submodule.subset_span <| mem_range_self _⟩ := by
  ext
  exact congr_arg ((↑) : span R (Set.range v) → M) <| Module.Basis.mk_apply _ _ _

