import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

theorem finite_of_fin_dim_affineIndependent [FiniteDimensional k V] {p : ι → P}
    (hi : AffineIndependent k p) : Finite ι := by
  nontriviality ι; inhabit ι
  rw [affineIndependent_iff_linearIndependent_vsub k p default] at hi
  letI : IsNoetherian k V := IsNoetherian.iff_fg.2 inferInstance
  exact
    (Set.finite_singleton default).finite_of_compl (Set.finite_coe_iff.1 hi.finite_of_isNoetherian)

