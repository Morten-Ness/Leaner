import Mathlib

variable {M A B : Type*}

variable [Monoid M] {x : M} (s : Submonoid M)

theorem prod_mem {M : Type*} [CommMonoid M] (S : Submonoid M) {ι : Type*} {t : Finset ι}
    {f : ι → M} (h : ∀ c ∈ t, f c ∈ S) : (∏ c ∈ t, f c) ∈ S := S.multiset_prod_mem (t.1.map f) fun _ hx =>
    let ⟨i, hi, hix⟩ := Multiset.mem_map.1 hx
    hix ▸ h i hi

