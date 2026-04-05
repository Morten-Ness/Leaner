import Mathlib

section

variable {ι R : Type*} [CommSemiring R]
  {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  {N : Type*} [AddCommMonoid N] [Module R N]

theorem Module.Basis.ext_multilinear [Finite ι] {f g : MultilinearMap R M N} {ιM : ι → Type*}
    (e : ∀ i, Basis (ιM i) R (M i))
    (h : ∀ v : (i : ι) → ιM i, (f fun i ↦ e i (v i)) = g fun i ↦ e i (v i)) : f = g := by
  cases nonempty_fintype ι
  classical
  ext m
  rcases Function.Surjective.piMap (fun i ↦ (e i).repr.symm.surjective) m with ⟨x, rfl⟩
  unfold Pi.map
  simp_rw [(e _).repr_symm_apply, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum_finset, map_smul_univ, h]

end

section

variable {ι R : Type*} [CommSemiring R]
  {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  {N : Type*} [AddCommMonoid N] [Module R N]

variable {κ : ι → Type*} (b : (i : ι) → Basis (κ i) R (M i))
  {ι' N : Type*} [AddCommMonoid N] [Module R N] (b' : Basis ι' R N)

variable [Fintype ι] [∀ i, Finite (κ i)]

theorem multilinearMap_apply (i : (Π i, κ i) × ι') :
    Module.Basis.multilinearMap b b' i =
      ((LinearMap.id (M := R)).smulRight (b' i.2)).compMultilinearMap
        (MultilinearMap.mkPiRing R ι 1 |>.compLinearMap fun i' => (b i').coord (i.1 i')) := by
  ext x
  simp +instances only [Module.Basis.multilinearMap, Module.Basis.coe_ofRepr, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply, LinearEquiv.multilinearMapCongrRight_symm_apply,
    Module.Basis.coe_repr_symm, LinearEquiv.multilinearMapCongrLeft_symm_apply, compLinearMap_apply,
    LinearEquiv.coe_coe, LinearMap.compMultilinearMap_apply, freeFinsuppEquiv_single, one_smul,
    Finsupp.linearCombination_single, Module.Basis.coord_apply, mkPiRing_apply, smul_eq_mul, mul_one,
    LinearMap.coe_smulRight, LinearMap.id_coe, id_eq, Subsingleton.elim (Fintype.ofFinite ι)]

end

section

variable {ι R : Type*} [CommSemiring R]
  {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  {N : Type*} [AddCommMonoid N] [Module R N]

variable {κ : ι → Type*} (b : (i : ι) → Basis (κ i) R (M i))
  {ι' N : Type*} [AddCommMonoid N] [Module R N] (b' : Basis ι' R N)

variable [Fintype ι] [∀ i, Finite (κ i)]

theorem multilinearMap_apply_apply (ii : (Π i, κ i) × ι') (v) :
    Module.Basis.multilinearMap b b' ii v = (∏ i, (b i).repr (v i) (ii.1 i)) • b' ii.2 := by
  simp [Module.Basis.multilinearMap_apply]

end
