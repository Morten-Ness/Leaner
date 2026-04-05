import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable {v : ι → M} {x y : M}

variable (hli : LinearIndependent R v) (hsp : ⊤ ≤ span R (range v))

theorem mk_repr : (Module.Basis.mk hli hsp).repr x = hli.repr ⟨x, hsp Submodule.mem_top⟩ := rfl

