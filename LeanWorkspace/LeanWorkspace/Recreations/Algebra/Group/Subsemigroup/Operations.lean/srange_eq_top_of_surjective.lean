import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

set_option backward.privateInPublic true in
private theorem srange_mk_aux_mul {f : M → N} (hf : ∀ (x y : M), f (x * y) = f x * f y)
    {x y : N} (hx : x ∈ Set.range f) (hy : y ∈ Set.range f) :
    x * y ∈ Set.range f := (MulHom.srange ⟨f, hf⟩).mul_mem hx hy


theorem srange_eq_top_of_surjective {N} [Mul N] (f : M →ₙ* N) (hf : Function.Surjective f) :
    f.srange = (⊤ : Subsemigroup N) := MulHom.srange_eq_top_iff_surjective.2 hf

