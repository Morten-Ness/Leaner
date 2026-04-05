import Mathlib

variable {ι : Sort uι} {R M N P : Type*}

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]

variable [Module R M] [Module R N] [Module R P]

variable {M₂ N₂ P₂ : Type*}

variable [AddCommMonoid M₂] [AddCommMonoid N₂] [AddCommMonoid P₂]

variable [Module R M₂] [Module R N₂] [Module R P₂]

theorem map_map₂ (f : P →ₗ[R] P₂) (g : M →ₗ[R] N →ₗ[R] P) (p : Submodule R M) (q : Submodule R N) :
    map f (Submodule.map₂ g p q) = Submodule.map₂ (g.compr₂ f) p q := map_iSup _ _ |>.trans <| iSup_congr fun _ => map_comp _ _ _ |>.symm

