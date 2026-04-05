import Mathlib

variable {R M A N : Type*} [CommRing R] [AddCommMonoid M] [Module R M]
  [CommRing A] [AddCommMonoid N] [Module A N] [Algebra R A] [Module R N] [IsScalarTower R A N]
  (f : M →ₗ[R] N)

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


theorem isTorsionFree_of_forall_isRegular (S : Submonoid R) (hS : ∀ s ∈ S, s ≠ 0 → IsRegular s)
    [IsTorsionFree R M] [IsLocalization S A] [IsLocalizedModule S f] : IsTorsionFree A N where
  isSMulRegular c hc x y hxy := by
    by_cases hS₀ : 0 ∈ S
    · have : Subsingleton N := (IsLocalizedModule.subsingleton_iff S f).2 fun _ ↦ ⟨0, hS₀, by simp⟩
      exact Subsingleton.elim ..
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S c
    obtain ⟨⟨m₁, t₁⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f x
    obtain ⟨⟨m₂, t₂⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f y
    replace hS : ∀ s ∈ S, IsRegular s := fun s hs ↦ hS s hs <| ne_of_mem_of_not_mem hs hS₀
    rw [IsLocalization.isRegular_mk' hS] at hc
    have (s : S) (x y : M) : s • x = s • y ↔ x = y := (hS _ s.2).isSMulRegular.eq_iff
    simp only [Function.uncurry_apply_pair, IsLocalizedModule.mk'_smul_mk', IsLocalizedModule.mk'_eq_mk'_iff, mul_smul, this,
      exists_const] at hxy ⊢
    simpa [smul_comm _ a, hc.isSMulRegular.eq_iff] using hxy

