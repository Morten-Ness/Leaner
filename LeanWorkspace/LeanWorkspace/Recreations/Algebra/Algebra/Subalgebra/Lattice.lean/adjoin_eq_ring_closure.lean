import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommRing R] [Ring A]

variable [Algebra R A] {s t : Set A}

theorem adjoin_eq_ring_closure (s : Set A) :
    (Algebra.adjoin R s).toSubring = Subring.closure (Set.range (algebraMap R A) ∪ s) := .symm <| Subring.closure_eq_of_le (by simp [Algebra.adjoin]) fun x hx =>
    Subsemiring.closure_induction Subring.subset_closure (Subring.zero_mem _) (Subring.one_mem _)
      (fun _ _ _ _ => Subring.add_mem _) (fun _ _ _ _ => Subring.mul_mem _) hx

