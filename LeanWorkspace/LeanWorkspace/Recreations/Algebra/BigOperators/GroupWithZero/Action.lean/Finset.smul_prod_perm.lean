import Mathlib

variable {M N γ : Type*}

variable [Monoid M] [CommMonoid N] [MulDistribMulAction M N]

variable {G : Type*} [Group G] [MulDistribMulAction G N]

theorem Finset.smul_prod_perm [Fintype G] (b : N) (g : G) :
    (g • ∏ h : G, h • b) = ∏ h : G, h • b := by
  simp only [smul_prod', smul_smul]
  exact Finset.prod_bijective (g * ·) (Group.mulLeft_bijective g) (by simp) (fun _ _ ↦ rfl)

