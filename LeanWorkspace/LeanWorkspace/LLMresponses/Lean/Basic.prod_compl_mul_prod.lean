FAIL
import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_compl_mul_prod [Fintype ι] [DecidableEq ι] (s : Finset ι) (f : ι → M) :
    (∏ i ∈ sᶜ, f i) * ∏ i ∈ s, f i = ∏ i, f i := by
  classical
  rw [← Finset.prod_union]
  · simpa [Finset.mem_compl] using (Finset.prod_univ_diff (t := s) f).symm
  · exact Finset.disjoint_compl_right
