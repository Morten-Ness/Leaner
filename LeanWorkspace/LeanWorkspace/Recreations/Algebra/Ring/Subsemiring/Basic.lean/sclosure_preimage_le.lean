import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable {s : Subsemiring R}

variable {σR σS : Type*}

variable [SetLike σR R] [SetLike σS S] [SubsemiringClass σR R] [SubsemiringClass σS S]

theorem sclosure_preimage_le (f : R →+* S) (s : Set S) : Subsemiring.closure (f ⁻¹' s) ≤ (Subsemiring.closure s).comap f := Subsemiring.closure_le.2 fun _ hx => SetLike.mem_coe.2 <| Subsemiring.mem_comap.2 <| Subsemiring.subset_closure hx

