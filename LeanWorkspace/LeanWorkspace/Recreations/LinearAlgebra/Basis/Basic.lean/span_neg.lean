import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable {v : ι → M} {x y : M}

variable (hli : LinearIndependent R v)

theorem span_neg {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {v : ι → M} (hli : LinearIndependent R v)
    (h : span R (Set.range v) = span R (Set.range (-v)) := by simp [← neg_range']) :
    Module.Basis.span hli.neg = ((Module.Basis.span hli).map <| (LinearEquiv.neg _).trans (.ofEq _ _ h)) := by
  ext; simp

