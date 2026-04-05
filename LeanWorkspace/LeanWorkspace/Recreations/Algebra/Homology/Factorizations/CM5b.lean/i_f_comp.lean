import Mathlib

variable {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C]
  {K L : CochainComplex C ℤ} (f : K ⟶ L)

set_option backward.isDefEq.respectTransparency false in
theorem i_f_comp (n : ℤ) : (CochainComplex.cm5b.i f).f n ≫
    (biprod.fst : mappingCone (𝟙 (CochainComplex.cm5b.I K)) ⊞ L ⟶ _).f n ≫
      (mappingCone.snd (𝟙 (CochainComplex.cm5b.I K))).v n n (add_zero n) = Function.Injective.ι (K.X n) := by
  simp [CochainComplex.cm5b.i]

