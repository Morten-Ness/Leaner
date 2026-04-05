import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

theorem NonUnitalSubring.toSubring_toNonUnitalSubring (S : NonUnitalSubring R) (h1 : (1 : R) ∈ S) :
    (NonUnitalSubring.toSubring S h1).toNonUnitalSubring = S := by cases S; rfl

