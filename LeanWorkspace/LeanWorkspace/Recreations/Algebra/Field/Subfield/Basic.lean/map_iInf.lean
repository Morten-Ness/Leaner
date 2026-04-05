import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem map_iInf {ι : Sort*} [Nonempty ι] (f : K →+* L) (s : ι → Subfield K) :
    (iInf s).map f = ⨅ i, (s i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective f.injective).image_iInter_eq (s := SetLike.coe ∘ s)

