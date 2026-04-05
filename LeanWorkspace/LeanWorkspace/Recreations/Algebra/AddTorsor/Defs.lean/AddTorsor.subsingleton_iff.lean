import Mathlib

theorem AddTorsor.subsingleton_iff (G P : Type*) [AddGroup G] [AddTorsor G P] :
    Subsingleton G ↔ Subsingleton P := by
  inhabit P
  exact (Equiv.vaddConst default).subsingleton_congr

