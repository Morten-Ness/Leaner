import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem map_map (g : N →* P) (f : M →* N) : (S.map f).map g = S.map (g.comp f) := SetLike.coe_injective <| image_image _ _ _

-- The simpNF linter says that the LHS can be simplified via `Submonoid.mem_map`.
-- However this is a higher priority lemma.
-- It seems the side condition `hf` is not applied by `simpNF`.
-- https://github.com/leanprover/std4/issues/207

