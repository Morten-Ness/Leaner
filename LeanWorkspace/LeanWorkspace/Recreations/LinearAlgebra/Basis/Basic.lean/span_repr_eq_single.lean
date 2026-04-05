import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable {v : ι → M} {x y : M}

variable (hli : LinearIndependent R v)

theorem span_repr_eq_single (i : ι)
    (hi : v i ∈ span R (Set.range v) := subset_span <| mem_range_self i) :
    (Module.Basis.span hli).repr ⟨v i, hi⟩ = single i 1 := by
  rw [← LinearEquiv.eq_symm_apply]
  simp [Module.Basis.span]

