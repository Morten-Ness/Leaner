FAIL
import Mathlib

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [AddTorsor V P]

variable [DivisionRing k] [Module k V]

theorem exists_affineBasis_of_finiteDimensional [Fintype ι] [FiniteDimensional k V]
    (h : Fintype.card ι = Module.finrank k V + 1) : Nonempty (AffineBasis ι k P) := by
  classical
  let e : Fin (Module.finrank k V + 1) ≃ ι :=
    Fintype.equivOfCardEq h.symm
  let b : AffineBasis (Fin (Module.finrank k V + 1)) k P := by
    simpa using (AffineSpace.affineBasisOfFiniteDimensional (k := k) (P := P))
  exact ⟨b.reindex e⟩
