import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

theorem iSup_induction {ι} (N : ι → LieSubmodule R L M) {motive : M → Prop} {x : M}
    (hx : x ∈ ⨆ i, N i) (mem : ∀ i, ∀ y ∈ N i, motive y) (zero : motive 0)
    (add : ∀ y z, motive y → motive z → motive (y + z)) : motive x := by
  rw [← LieSubmodule.mem_toSubmodule, LieSubmodule.iSup_toSubmodule] at hx
  exact Submodule.iSup_induction (motive := motive) (fun i ↦ (N i : Submodule R M)) hx mem zero add

