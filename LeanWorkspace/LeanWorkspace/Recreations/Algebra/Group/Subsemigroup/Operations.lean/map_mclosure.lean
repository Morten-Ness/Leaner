import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

set_option backward.privateInPublic true in
private theorem srange_mk_aux_mul {f : M → N} (hf : ∀ (x y : M), f (x * y) = f x * f y)
    {x y : N} (hx : x ∈ Set.range f) (hy : y ∈ Set.range f) :
    x * y ∈ Set.range f := (MulHom.srange ⟨f, hf⟩).mul_mem hx hy


theorem map_mclosure (f : M →ₙ* N) (s : Set M) : (closure s).map f = closure (f '' s) := Set.image_preimage.l_comm_of_u_comm (Subsemigroup.gc_map_comap f) (Subsemigroup.gi N).gc (Subsemigroup.gi M).gc
    fun _ ↦ rfl

