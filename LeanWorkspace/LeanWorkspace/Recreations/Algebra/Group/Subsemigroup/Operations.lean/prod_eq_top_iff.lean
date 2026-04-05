import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

set_option backward.privateInPublic true in
private theorem srange_mk_aux_mul {f : M → N} (hf : ∀ (x y : M), f (x * y) = f x * f y)
    {x y : N} (hx : x ∈ Set.range f) (hy : y ∈ Set.range f) :
    x * y ∈ Set.range f := (MulHom.srange ⟨f, hf⟩).mul_mem hx hy


theorem prod_eq_top_iff [Nonempty M] [Nonempty N] {s : Subsemigroup M} {t : Subsemigroup N} :
    s.prod t = ⊤ ↔ s = ⊤ ∧ t = ⊤ := by
  simp only [eq_top_iff, Subsemigroup.le_prod_iff, ← MulHom.srange_eq_map, Subsemigroup.srange_fst, Subsemigroup.srange_snd]

