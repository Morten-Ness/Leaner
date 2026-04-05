import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

set_option backward.privateInPublic true in
private theorem srange_mk_aux_mul {f : M → N} (hf : ∀ (x y : M), f (x * y) = f x * f y)
    {x y : N} (hx : x ∈ Set.range f) (hy : y ∈ Set.range f) :
    x * y ∈ Set.range f := (MulHom.srange ⟨f, hf⟩).mul_mem hx hy


theorem eq_top_iff' : S = ⊤ ↔ ∀ x : M, x ∈ S := eq_top_iff.trans ⟨fun h m => h <| mem_top m, fun h m _ => h m⟩

