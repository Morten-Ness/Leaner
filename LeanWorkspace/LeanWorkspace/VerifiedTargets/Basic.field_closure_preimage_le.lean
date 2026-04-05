import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable {s : Subfield K}

theorem field_closure_preimage_le (f : K →+* L) (s : Set L) :
    Subfield.closure (f ⁻¹' s) ≤ (Subfield.closure s).comap f := Subfield.closure_le.2 fun _ hx => SetLike.mem_coe.2 <| Subfield.mem_comap.2 <| Subfield.subset_closure hx

