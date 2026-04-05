import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable {s : Subring R}

theorem closure_preimage_le (f : R →+* S) (s : Set S) : Subring.closure (f ⁻¹' s) ≤ (Subring.closure s).comap f := Subring.closure_le.2 fun _ hx => SetLike.mem_coe.2 <| Subring.mem_comap.2 <| Subring.subset_closure hx

