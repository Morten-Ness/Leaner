import Mathlib

variable {M N γ : Type*}

variable [Monoid M] [CommMonoid N] [MulDistribMulAction M N]

variable {G : Type*} [Group G] [MulDistribMulAction G N]

theorem smul_finprod_perm [Finite G] (b : N) (g : G) :
    (g • ∏ᶠ h : G, h • b) = ∏ᶠ h : G, h • b := by
  cases nonempty_fintype G
  simp only [finprod_eq_prod_of_fintype, Finset.smul_prod_perm]

