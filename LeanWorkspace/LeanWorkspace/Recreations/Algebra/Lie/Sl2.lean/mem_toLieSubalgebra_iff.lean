import Mathlib

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable {h e f : L}

theorem mem_toLieSubalgebra_iff {x : L} {t : IsSl2Triple h e f} :
    x ∈ t.toLieSubalgebra R ↔ ∃ c₁ c₂ c₃ : R, x = c₁ • e + c₂ • f + c₃ • ⁅e, f⁆ := by
  simp_rw [t.lie_e_f, IsSl2Triple.toLieSubalgebra, ← LieSubalgebra.mem_toSubmodule, Submodule.mem_span_triple,
    eq_comm]

