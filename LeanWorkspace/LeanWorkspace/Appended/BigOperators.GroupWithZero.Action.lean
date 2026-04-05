import Mathlib

section

variable {M N γ : Type*}

variable [Monoid M] [CommMonoid N] [MulDistribMulAction M N]

theorem Finset.smul_prod' {r : M} {f : γ → N} {s : Finset γ} :
    (r • ∏ x ∈ s, f x) = ∏ x ∈ s, r • f x := map_prod (MulDistribMulAction.toMonoidHom N r) f s

end

section

variable {M N γ : Type*}

variable [Monoid M] [CommMonoid N] [MulDistribMulAction M N]

variable {G : Type*} [Group G] [MulDistribMulAction G N]

theorem Finset.smul_prod_perm [Fintype G] (b : N) (g : G) :
    (g • ∏ h : G, h • b) = ∏ h : G, h • b := by
  simp only [smul_prod', smul_smul]
  exact Finset.prod_bijective (g * ·) (Group.mulLeft_bijective g) (by simp) (fun _ _ ↦ rfl)

end

section

variable {M N γ : Type*}

variable [AddCommMonoid N] [DistribSMul M N] {r : M}

theorem Finset.smul_sum {f : γ → N} {s : Finset γ} :
    (r • ∑ x ∈ s, f x) = ∑ x ∈ s, r • f x := map_sum (DistribSMul.toAddMonoidHom N r) f s

end

section

variable {M N γ : Type*}

variable [Monoid M] [Monoid N] [MulDistribMulAction M N]

theorem List.smul_prod' {r : M} {l : List N} : r • l.prod = (l.map (r • ·)).prod := map_list_prod (MulDistribMulAction.toMonoidHom N r) l

end

section

variable {M N γ : Type*}

variable [AddMonoid N] [DistribSMul M N]

theorem List.smul_sum {r : M} {l : List N} : r • l.sum = (l.map (r • ·)).sum := map_list_sum (DistribSMul.toAddMonoidHom N r) l

end

section

variable {M N γ : Type*}

variable [Monoid M] [CommMonoid N] [MulDistribMulAction M N]

theorem Multiset.smul_prod' {r : M} {s : Multiset N} : r • s.prod = (s.map (r • ·)).prod := (MulDistribMulAction.toMonoidHom N r).map_multiset_prod s

end

section

variable {M N γ : Type*}

variable [AddCommMonoid N] [DistribSMul M N] {r : M}

theorem Multiset.smul_sum {s : Multiset N} : r • s.sum = (s.map (r • ·)).sum := (DistribSMul.toAddMonoidHom N r).map_multiset_sum s

end

section

variable {M N γ : Type*}

variable {ι : Type*}

theorem prod_smul
    [CommMonoid N] [CommMonoid M] [MulAction M N] [IsScalarTower M N N] [SMulCommClass M N N]
    (s : Finset ι) (b : ι → M) (f : ι → N) :
    ∏ i ∈ s, b i • f i = (∏ i ∈ s, b i) • ∏ i ∈ s, f i := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons _ _ hj ih => rw [prod_cons, ih, smul_mul_smul_comm, ← prod_cons hj, ← prod_cons hj]

end

section

variable {M N γ : Type*}

variable [Monoid M] [CommMonoid N] [MulDistribMulAction M N]

theorem smul_finprod' {ι : Sort*} [Finite ι] {f : ι → N} (r : M) :
    r • ∏ᶠ x : ι, f x = ∏ᶠ x : ι, r • (f x) := by
  cases nonempty_fintype (PLift ι)
  simp only [finprod_eq_prod_plift_of_mulSupport_subset (s := Finset.univ) (by simp),
    Finset.smul_prod']

end

section

variable {M N γ : Type*}

variable [Monoid M] [CommMonoid N] [MulDistribMulAction M N]

variable {G : Type*} [Group G] [MulDistribMulAction G N]

theorem smul_finprod_perm [Finite G] (b : N) (g : G) :
    (g • ∏ᶠ h : G, h • b) = ∏ᶠ h : G, h • b := by
  cases nonempty_fintype G
  simp only [finprod_eq_prod_of_fintype, Finset.smul_prod_perm]

end

section

variable {M N γ : Type*}

variable [AddCommMonoid N] [DistribSMul M N] {r : M}

theorem smul_finsum_mem {f : γ → N} {s : Set γ} (hs : s.Finite) :
    r • ∑ᶠ x ∈ s, f x = ∑ᶠ x ∈ s, r • f x := (DistribSMul.toAddMonoidHom N r).map_finsum_mem f hs

end
