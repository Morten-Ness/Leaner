import Mathlib

variable {ι α β M N G k R : Type*}

variable [Fintype ι] [CommMonoid M] [PartialOrder M] [IsOrderedCancelMonoid M] {f : ι → M}

theorem one_lt_prod (hf : 1 < f) : 1 < ∏ i, f i := Finset.one_lt_prod' (fun _ _ ↦ hf.le _) <| by simpa using (Pi.lt_def.1 hf).2

