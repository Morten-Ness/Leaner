import Mathlib

open scoped Finset

variable {ι κ M N R α : Type*}

variable {I : Type*} [DecidableEq I] {M : I → Type*}

variable [∀ i, CommMonoid (M i)]

theorem MonoidHom.functions_ext [Finite I] (N : Type*) [CommMonoid N] (g h : (∀ i, M i) →* N)
    (H : ∀ i x, g (Pi.mulSingle i x) = h (Pi.mulSingle i x)) : g = h := by
  cases nonempty_fintype I
  ext k
  rw [← Finset.univ_prod_mulSingle k, map_prod, map_prod]
  simp only [H]

