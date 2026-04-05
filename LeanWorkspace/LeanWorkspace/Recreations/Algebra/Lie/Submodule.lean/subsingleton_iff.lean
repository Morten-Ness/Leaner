import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

theorem subsingleton_iff : Subsingleton (LieSubmodule R L M) ↔ Subsingleton M := have h : Subsingleton (LieSubmodule R L M) ↔ Subsingleton (Submodule R M) := by
    rw [← subsingleton_iff_bot_eq_top, ← subsingleton_iff_bot_eq_top, ← LieSubmodule.toSubmodule_inj,
      LieSubmodule.top_toSubmodule, LieSubmodule.bot_toSubmodule]
  h.trans <| Submodule.subsingleton_iff R

