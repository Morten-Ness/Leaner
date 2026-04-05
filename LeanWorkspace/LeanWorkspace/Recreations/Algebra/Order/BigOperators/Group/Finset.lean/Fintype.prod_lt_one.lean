import Mathlib

variable {ι α β M N G k R : Type*}

variable [Fintype ι] [CommMonoid M] [PartialOrder M] [IsOrderedCancelMonoid M] {f : ι → M}

theorem prod_lt_one (hf : f < 1) : ∏ i, f i < 1 := Finset.prod_lt_one' (fun _ _ ↦ hf.le _) <| by simpa using (Pi.lt_def.1 hf).2

