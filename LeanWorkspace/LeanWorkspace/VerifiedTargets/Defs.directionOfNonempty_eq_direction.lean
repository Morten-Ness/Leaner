import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem directionOfNonempty_eq_direction {s : AffineSubspace k P} (h : (s : Set P).Nonempty) :
    AffineSubspace.directionOfNonempty h = s.direction := by
  refine le_antisymm ?_ (Submodule.span_le.2 Set.Subset.rfl)
  rw [← SetLike.coe_subset_coe, AffineSubspace.directionOfNonempty, AffineSubspace.direction, Submodule.coe_set_mk,
    AddSubmonoid.coe_set_mk]
  exact vsub_set_subset_vectorSpan k _

