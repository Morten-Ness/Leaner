import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem torsionBySet_le_torsionBySet_of_subset {s t : Set R} (st : s ⊆ t) :
    Submodule.torsionBySet R M t ≤ Submodule.torsionBySet R M s := sInf_le_sInf fun _ ⟨a, ha, h⟩ => ⟨a, st ha, h⟩

