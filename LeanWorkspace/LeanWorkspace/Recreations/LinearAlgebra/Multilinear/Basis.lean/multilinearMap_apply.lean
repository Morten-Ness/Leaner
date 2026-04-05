import Mathlib

variable {ι R : Type*} [CommSemiring R]
  {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  {N : Type*} [AddCommMonoid N] [Module R N]

variable {κ : ι → Type*} (b : (i : ι) → Basis (κ i) R (M i))
  {ι' N : Type*} [AddCommMonoid N] [Module R N] (b' : Basis ι' R N)

variable [Fintype ι] [∀ i, Finite (κ i)]

theorem multilinearMap_apply (i : (Π i, κ i) × ι') :
    Basis.multilinearMap b b' i =
      ((LinearMap.id (M := R)).smulRight (b' i.2)).compMultilinearMap
        (MultilinearMap.mkPiRing R ι 1 |>.compLinearMap fun i' => (b i').coord (i.1 i')) := by
  ext x
  simp +instances only [Basis.multilinearMap, Basis.coe_ofRepr, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply, LinearEquiv.multilinearMapCongrRight_symm_apply,
    Basis.coe_repr_symm, LinearEquiv.multilinearMapCongrLeft_symm_apply, compLinearMap_apply,
    LinearEquiv.coe_coe, LinearMap.compMultilinearMap_apply, freeFinsuppEquiv_single, one_smul,
    Finsupp.linearCombination_single, Basis.coord_apply, mkPiRing_apply, smul_eq_mul, mul_one,
    LinearMap.coe_smulRight, LinearMap.id_coe, id_eq, Subsingleton.elim (Fintype.ofFinite ι)]

