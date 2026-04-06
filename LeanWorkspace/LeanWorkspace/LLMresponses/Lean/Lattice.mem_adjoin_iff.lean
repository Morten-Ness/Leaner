FAIL
import Mathlib

universe uR uS uA uB

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommRing R] [Ring A]

variable [Algebra R A] {s t : Set A}

theorem mem_adjoin_iff {s : Set A} {x : A} :
    x ∈ Algebra.adjoin R s ↔ x ∈ Subring.closure (Set.range (algebraMap R A) ∪ s) := by
  rw [Algebra.adjoin_eq_closure]
  rfl
