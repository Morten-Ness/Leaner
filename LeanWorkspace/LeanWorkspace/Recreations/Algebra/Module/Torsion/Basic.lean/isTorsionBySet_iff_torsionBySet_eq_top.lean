import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem isTorsionBySet_iff_torsionBySet_eq_top :
    IsTorsionBySet R M s ↔ Submodule.torsionBySet R M s = ⊤ := ⟨fun h => eq_top_iff.mpr fun _ _ => (Submodule.mem_torsionBySet_iff _ _).mpr <| @h _, fun h x => by
    rw [← Submodule.mem_torsionBySet_iff, h]
    trivial⟩

