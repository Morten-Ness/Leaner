import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable {v : ι → M} {x y : M}

variable (hli : LinearIndependent R v) (hsp : ⊤ ≤ span R (range v))

theorem mk_apply (i : ι) : Module.Basis.mk hli hsp i = v i := show Finsupp.linearCombination _ v _ = v i by simp

