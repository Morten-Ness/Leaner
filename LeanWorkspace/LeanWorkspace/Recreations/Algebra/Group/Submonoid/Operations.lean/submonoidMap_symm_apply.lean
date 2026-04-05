import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {S} {T : Submonoid M}

theorem submonoidMap_symm_apply (e : M ≃* N) (S : Submonoid M) (g : S.map (e : M →* N)) :
    (e.submonoidMap S).symm g = ⟨e.symm g, SetLike.mem_coe.1 <| Set.mem_image_equiv.1 g.2⟩ := rfl

