import Mathlib

open scoped Polynomial

variable {R : Type*}

variable {F : Type u} {K : Type v} {L : Type w}

variable [CommRing K] [Field L] [Field F]

variable (i : K →+* L)

theorem splits_id_iff_splits {f : K[X]} :
    ((f.map i).map (RingHom.id L)).Splits ↔ (f.map i).Splits := by
  rw [map_id]

