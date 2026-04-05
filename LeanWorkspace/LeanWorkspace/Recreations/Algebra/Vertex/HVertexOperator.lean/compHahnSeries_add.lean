import Mathlib

variable {Γ : Type*} [PartialOrder Γ] {R : Type*} {V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

variable {Γ Γ' : Type*} [PartialOrder Γ] [PartialOrder Γ'] {R : Type*}
  [CommRing R] {U V W : Type*} [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] (A : HVertexOperator Γ R V W) (B : HVertexOperator Γ' R U V)

set_option backward.isDefEq.respectTransparency false in
theorem compHahnSeries_add (u v : U) :
    HVertexOperator.compHahnSeries A B (u + v) = HVertexOperator.compHahnSeries A B u + HVertexOperator.compHahnSeries A B v := by
  ext
  simp only [compHahnSeries_coeff, map_add, coeff_apply_apply, HahnSeries.coeff_add', Pi.add_apply]
  rw [← HahnSeries.coeff_add]

