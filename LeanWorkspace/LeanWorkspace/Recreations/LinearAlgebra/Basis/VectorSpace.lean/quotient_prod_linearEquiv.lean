import Mathlib

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem quotient_prod_linearEquiv (p : Submodule K V) : Nonempty (((V ⧸ p) × p) ≃ₗ[K] V) := let ⟨q, hq⟩ := p.exists_isCompl
  Nonempty.intro <|
    ((quotientEquivOfIsCompl p q hq).prodCongr (LinearEquiv.refl _ _)).trans
      (prodEquivOfIsCompl q p hq.symm)

