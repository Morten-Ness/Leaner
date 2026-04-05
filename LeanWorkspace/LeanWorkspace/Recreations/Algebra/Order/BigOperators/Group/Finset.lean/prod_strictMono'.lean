import Mathlib

variable {ι α β M N G k R : Type*}

variable [Fintype ι] [CommMonoid M] [PartialOrder M] [IsOrderedCancelMonoid M] {f : ι → M}

theorem prod_strictMono' : StrictMono fun f : ι → M ↦ ∏ x, f x := fun _ _ hfg ↦
  let ⟨hle, i, hlt⟩ := Pi.lt_def.mp hfg
  Finset.prod_lt_prod' (fun i _ ↦ hle i) ⟨i, Finset.mem_univ i, hlt⟩

