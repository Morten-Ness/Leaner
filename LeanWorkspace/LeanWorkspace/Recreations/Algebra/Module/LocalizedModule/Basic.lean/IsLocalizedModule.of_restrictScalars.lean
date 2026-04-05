import Mathlib

variable {R : Type*} [CommSemiring R] (S : Submonoid R)

variable {M M' M'' : Type*} [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid M'']

variable {A : Type*} [CommSemiring A] [Algebra R A] [Module A M'] [IsLocalization S A]

variable [Module R M] [Module R M'] [Module R M''] [IsScalarTower R A M']

variable (f : M →ₗ[R] M') (g : M →ₗ[R] M'')

private theorem example_localization_eq_localizedModule
    {R} [CommSemiring R] (S : Submonoid R) : Localization S = LocalizedModule S R := by
  with_reducible rfl


set_option backward.isDefEq.respectTransparency false in
private theorem example_oreLocalizationInstMonoid_eq_localizedModuleInstMonoid :
    OreLocalization.instMonoid = LocalizedModule.instMonoid (A := R) (S := S) := by
  with_reducible_and_instances rfl


set_option backward.isDefEq.respectTransparency false in
private theorem example_oreLocalizationInstCommRing_eq_localizedModuleInstCommRing
    {R : Type*} [CommRing R] {S : Submonoid R} :
    OreLocalization.instCommRing = (LocalizedModule.instCommRing : CommRing R[S⁻¹]) := by
  with_reducible_and_instances rfl


set_option backward.privateInPublic true in
private theorem one_smul_aux (p : LocalizedModule S M) : (1 : T) • p = p := by
  induction p with | _ m s
  rw [show (1 : T) = IsLocalization.mk' T (1 : R) (1 : S) by rw [IsLocalization.mk'_one, map_one]]
  rw [LocalizedModule.mk'_smul_mk, one_smul, one_mul]


set_option backward.privateInPublic true in
private theorem mul_smul_aux (x y : T) (p : LocalizedModule S M) :
    (x * y) • p = x • y • p := by
  induction p with | _ m s
  rw [← IsLocalization.mk'_sec (M := S) T x, ← IsLocalization.mk'_sec (M := S) T y]
  simp_rw [← IsLocalization.mk'_mul, LocalizedModule.mk'_smul_mk, ← mul_smul, mul_assoc]


set_option backward.privateInPublic true in
private theorem smul_add_aux (x : T) (p q : LocalizedModule S M) :
    x • (p + q) = x • p + x • q := by
  induction p with | _ m s
  induction q with | _ n t
  rw [LocalizedModule.smul_def, LocalizedModule.smul_def, LocalizedModule.mk_add_mk, LocalizedModule.mk_add_mk]
  rw [show x • _ = IsLocalization.mk' T _ _ • _ by rw [IsLocalization.mk'_sec (M := S) T]]
  rw [← IsLocalization.mk'_cancel _ _ (IsLocalization.sec S x).2, LocalizedModule.mk'_smul_mk]
  congr 1
  · simp only [Submonoid.smul_def, smul_add, ← mul_smul, Submonoid.coe_mul]; ring_nf
  · rw [mul_mul_mul_comm] -- ring does not work here


set_option backward.privateInPublic true in
private theorem smul_zero_aux (x : T) : x • (0 : LocalizedModule S M) = 0 := by
  conv => lhs; rw [← LocalizedModule.zero_mk 1, LocalizedModule.smul_def, smul_zero, LocalizedModule.zero_mk]


set_option backward.privateInPublic true in
private theorem add_smul_aux (x y : T) (p : LocalizedModule S M) :
    (x + y) • p = x • p + y • p := by
  induction p with | _ m s
  rw [LocalizedModule.smul_def T x, LocalizedModule.smul_def T y, LocalizedModule.mk_add_mk, show (x + y) • _ = IsLocalization.mk' T _ _ • _ by
    rw [← IsLocalization.mk'_sec (M := S) T x, ← IsLocalization.mk'_sec (M := S) T y,
      ← IsLocalization.mk'_add, IsLocalization.mk'_cancel _ _ s], LocalizedModule.mk'_smul_mk, ← smul_assoc,
    ← smul_assoc, ← add_smul]
  congr 1
  · simp only [Submonoid.smul_def, Submonoid.coe_mul, smul_eq_mul]; ring_nf
  · rw [mul_mul_mul_comm, mul_assoc] -- ring does not work here


set_option backward.privateInPublic true in
private theorem zero_smul_aux (p : LocalizedModule S M) : (0 : T) • p = 0 := by
  induction p with | _ m s
  rw [show (0 : T) = IsLocalization.mk' T (0 : R) (1 : S) by rw [IsLocalization.mk'_zero],
    LocalizedModule.mk'_smul_mk, zero_smul, LocalizedModule.zero_mk]


set_option backward.isDefEq.respectTransparency false in
private theorem example_oreLocalizationInstAlgebra_eq_localizedModuleAlgebra' :
    OreLocalization.instAlgebra = (algebra' : Algebra R (LocalizedModule S R)) := by
  with_reducible_and_instances rfl


theorem IsLocalizedModule.of_restrictScalars (S : Submonoid R)
    {N : Type*} [AddCommMonoid N] [Module R N] [Module A M] [Module A N]
    [IsScalarTower R A M] [IsScalarTower R A N]
    (f : M →ₗ[A] N) [IsLocalizedModule S (f.restrictScalars R)] :
    IsLocalizedModule (Algebra.algebraMapSubmonoid A S) f where
  map_units x := by
    obtain ⟨_, x, hx, rfl⟩ := x
    have := IsLocalizedModule.map_units (f.restrictScalars R) ⟨x, hx⟩
    simp only [← IsScalarTower.algebraMap_apply, Module.End.isUnit_iff] at this ⊢
    exact this
  surj y := by
    obtain ⟨⟨x, t⟩, e⟩ := IsLocalizedModule.surj S (f.restrictScalars R) y
    exact ⟨⟨x, ⟨_, t, t.2, rfl⟩⟩, by simpa [Submonoid.smul_def] using e⟩
  exists_of_eq {x₁ x₂} e := by
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f.restrictScalars R) e
    refine ⟨⟨_, c, c.2, rfl⟩, by simpa [Submonoid.smul_def]⟩

