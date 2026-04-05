import Mathlib

variable {R S : Type u} [Semiring R] [Semiring S] {T : Type v} [Semiring T]

theorem Ideal.spanFinrank_map_le_of_fg (f : R →+* T) {I : Ideal R} (hI : I.FG) :
    (I.map f).spanFinrank ≤ I.spanFinrank := by
  rw [← Submodule.FG.spanRank_le_iff (hI.map f), ← Cardinal.lift_le.{u}, Cardinal.lift_natCast,
    ← Cardinal.lift_natCast.{v}, ← Submodule.FG.spanRank_eq_spanFinrank hI]
  exact I.lift_spanRank_map_le f

