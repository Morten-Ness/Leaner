import Mathlib

open scoped Finset

variable {ι κ M N R α : Type*}

theorem prod_mk_prod [CommMonoid M] [CommMonoid N] (s : Finset ι) (f : ι → M) (g : ι → N) :
    (∏ x ∈ s, f x, ∏ x ∈ s, g x) = ∏ x ∈ s, (f x, g x) := haveI := Classical.decEq ι
  Finset.induction_on s rfl (by simp +contextual [Prod.ext_iff])

