import Mathlib

variable {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C]
  {K L : CochainComplex C ℤ} (f : K ⟶ L)

set_option backward.isDefEq.respectTransparency false in
theorem fac : CochainComplex.cm5b.i f ≫ p K L = f := by simp [CochainComplex.cm5b.i]

