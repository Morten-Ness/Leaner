import Mathlib

variable {R : Type*} [CommRing R] [StrongRankCondition R] (E : LinearRecurrence R)

theorem solSpace_rank : Module.rank R E.solSpace = E.order := letI := nontrivial_of_invariantBasisNumber R
  @rank_fin_fun R _ _ E.order ▸ E.toInit.rank_eq

