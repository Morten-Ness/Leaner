import Mathlib

variable {R S : Type u} [Semiring R] [Semiring S] {T : Type v} [Semiring T]

theorem Ideal.spanFinrank_map_eq_of_ringEquiv (f : R ≃+* T) (I : Ideal R) :
    (I.map f).spanFinrank = I.spanFinrank := by
  rw [Submodule.spanFinrank, Submodule.spanFinrank, ← Cardinal.toNat_lift.{u, v},
    ← Cardinal.toNat_lift.{v, u}, I.lift_spanRank_map_eq_of_ringEquiv f]

