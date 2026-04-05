import Mathlib

variable {R : Type*} [CommSemiring R] (E : LinearRecurrence R)

theorem sol_eq_of_eq_init (u v : ℕ → R) (hu : E.IsSolution u) (hv : E.IsSolution v) :
    u = v ↔ Set.EqOn u v ↑(range E.order) := by
  refine Iff.intro (fun h x _ ↦ h ▸ rfl) ?_
  intro h
  set u' : ↥E.solSpace := ⟨u, hu⟩
  set v' : ↥E.solSpace := ⟨v, hv⟩
  change u'.val = v'.val
  suffices h' : u' = v' from h' ▸ rfl
  rw [← E.toInit.toEquiv.apply_eq_iff_eq, LinearEquiv.coe_toEquiv]
  ext x
  exact mod_cast h (mem_range.mpr x.2)

