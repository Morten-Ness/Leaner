import Mathlib

variable {M A B : Type*}

variable [Monoid M] [SetLike B M] [SubmonoidClass B M] {x : M} {S : B}

theorem prod_mem {M : Type*} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] {ι : Type*}
    {t : Finset ι} {f : ι → M} (h : ∀ c ∈ t, f c ∈ S) : (∏ c ∈ t, f c) ∈ S := multiset_prod_mem (t.1.map f) fun _x hx =>
    let ⟨i, hi, hix⟩ := Multiset.mem_map.1 hx
    hix ▸ h i hi

