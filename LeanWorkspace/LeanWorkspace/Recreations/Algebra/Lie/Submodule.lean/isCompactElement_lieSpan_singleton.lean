import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

variable (R L) (s : Set M)

theorem isCompactElement_lieSpan_singleton (m : M) :
    IsCompactElement (LieSubmodule.lieSpan R L {m}) := by
  rw [CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le]
  intro s hne hdir hsup
  replace hsup : m ∈ (↑(sSup s) : Set M) := (SetLike.le_def.mp hsup) (LieSubmodule.subset_lieSpan rfl)
  suffices (↑(sSup s) : Set M) = ⋃ N ∈ s, ↑N by simp_all
  replace hne : Nonempty s := Set.nonempty_coe_sort.mpr hne
  have := Submodule.coe_iSup_of_directed _ hdir.directed_val
  simp_rw [← LieSubmodule.iSup_toSubmodule, Set.iUnion_coe_set, LieSubmodule.coe_toSubmodule] at this
  rw [← this, SetLike.coe_set_eq, sSup_eq_iSup, iSup_subtype]

