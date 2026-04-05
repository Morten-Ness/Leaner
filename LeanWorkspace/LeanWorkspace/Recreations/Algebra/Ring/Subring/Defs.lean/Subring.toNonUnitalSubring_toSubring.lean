import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

theorem Subring.toNonUnitalSubring_toSubring (S : Subring R) :
    S.toNonUnitalSubring.toSubring S.one_mem = S := by cases S; rfl

