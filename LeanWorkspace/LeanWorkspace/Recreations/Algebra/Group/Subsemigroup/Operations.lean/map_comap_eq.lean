import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N]

set_option backward.privateInPublic true in
private theorem srange_mk_aux_mul {f : M → N} (hf : ∀ (x y : M), f (x * y) = f x * f y)
    {x y : N} (hx : x ∈ Set.range f) (hy : y ∈ Set.range f) :
    x * y ∈ Set.range f := (MulHom.srange ⟨f, hf⟩).mul_mem hx hy


theorem map_comap_eq (f : M →ₙ* N) (S : Subsemigroup N) : (S.comap f).map f = S ⊓ f.srange := SetLike.coe_injective Set.image_preimage_eq_inter_range

