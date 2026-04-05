import Mathlib

variable {R S : Type u} [Semiring R] [Semiring S] {T : Type v} [Semiring T]

theorem Ideal.lift_spanRank_map_eq_of_ringEquiv (f : R ≃+* T) (I : Ideal R) :
    Cardinal.lift.{u} (I.map f).spanRank = Cardinal.lift.{v} I.spanRank := by
  apply (I.lift_spanRank_map_le (f : R →+* T)).antisymm
  nth_rw 1 [← Ideal.map_of_equiv f (I := I)]
  exact Ideal.lift_spanRank_map_le (f.symm : T →+* R) _

