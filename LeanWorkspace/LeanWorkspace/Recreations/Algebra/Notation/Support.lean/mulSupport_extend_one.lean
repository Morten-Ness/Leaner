import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem mulSupport_extend_one {f : ι → κ} {g : ι → N} (hf : f.Injective) :
    Function.mulSupport (f.extend g 1) = f '' Function.mulSupport g := Function.mulSupport_extend_one_subset.antisymm <| by
    rintro _ ⟨x, hx, rfl⟩; rwa [Function.mem_mulSupport, hf.extend_apply]

