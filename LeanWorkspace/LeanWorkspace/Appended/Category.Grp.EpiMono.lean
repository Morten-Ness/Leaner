import Mathlib

section

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem agree : f.hom.range = { x | GrpCat.SurjectiveOfEpiAuxs.h x = GrpCat.SurjectiveOfEpiAuxs.g x } := by
  refine Set.ext fun b => ⟨?_, fun hb : GrpCat.SurjectiveOfEpiAuxs.h b = GrpCat.SurjectiveOfEpiAuxs.g b => by_contradiction fun r => ?_⟩
  · rintro ⟨a, rfl⟩
    change GrpCat.SurjectiveOfEpiAuxs.h (f a) = GrpCat.SurjectiveOfEpiAuxs.g (f a)
    ext ⟨⟨_, ⟨y, rfl⟩⟩⟩
    · rw [GrpCat.SurjectiveOfEpiAuxs.g_apply_fromCoset]
      by_cases m : y ∈ f.hom.range
      · rw [GrpCat.SurjectiveOfEpiAuxs.h_apply_fromCoset' _ _ _ m, GrpCat.SurjectiveOfEpiAuxs.fromCoset_eq_of_mem_range _ m]
        change fromCoset _ = fromCoset ⟨f a • (y • _), _⟩
        simp only [← GrpCat.SurjectiveOfEpiAuxs.fromCoset_eq_of_mem_range _ (Subgroup.mul_mem _ ⟨a, rfl⟩ m), smul_smul]
      · rw [GrpCat.SurjectiveOfEpiAuxs.h_apply_fromCoset_nin_range f (f a) ⟨_, rfl⟩ _ m]
        simp only [leftCoset_assoc]
    · rw [GrpCat.SurjectiveOfEpiAuxs.g_apply_infinity, GrpCat.SurjectiveOfEpiAuxs.h_apply_infinity f (f a) ⟨_, rfl⟩]
  · have eq1 : (GrpCat.SurjectiveOfEpiAuxs.h b) (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) =
        fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩ := by
      change ((τ).symm.trans (GrpCat.SurjectiveOfEpiAuxs.g b)).trans τ _ = _
      dsimp [GrpCat.SurjectiveOfEpiAuxs.tau]
      simp [GrpCat.SurjectiveOfEpiAuxs.g_apply_infinity f]
    have eq2 :
        GrpCat.SurjectiveOfEpiAuxs.g b (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) = fromCoset ⟨b • ↑f.hom.range, b, rfl⟩ :=
      rfl
    exact (GrpCat.SurjectiveOfEpiAuxs.fromCoset_ne_of_nin_range _ r).symm (by rw [← eq1, ← eq2, DFunLike.congr_fun hb])

end

section

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem comp_eq : (f ≫ ofHom GrpCat.SurjectiveOfEpiAuxs.g) = f ≫ ofHom GrpCat.SurjectiveOfEpiAuxs.h := by
  ext a
  simp only [hom_comp, hom_ofHom, MonoidHom.coe_comp, Function.comp_apply]
  have : f a ∈ { b | GrpCat.SurjectiveOfEpiAuxs.h b = GrpCat.SurjectiveOfEpiAuxs.g b } := by
    rw [← GrpCat.SurjectiveOfEpiAuxs.agree]
    use a
  rw [this]

end

section

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem fromCoset_eq_of_mem_range {b : B} (hb : b ∈ f.hom.range) :
    fromCoset ⟨b • ↑f.hom.range, b, rfl⟩ = fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩ := by
  congr
  nth_rw 2 [show (f.hom.range : Set B) = (1 : B) • f.hom.range from (one_leftCoset _).symm]
  rw [leftCoset_eq_iff, mul_one]
  exact Subgroup.inv_mem _ hb

example (G : Type) [Group G] (S : Subgroup G) : Set G := S

end

section

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem fromCoset_ne_of_nin_range {b : B} (hb : b ∉ f.hom.range) :
    fromCoset ⟨b • ↑f.hom.range, b, rfl⟩ ≠ fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩ := by
  intro r
  simp only [fromCoset.injEq, Subtype.mk.injEq] at r
  nth_rw 2 [show (f.hom.range : Set B) = (1 : B) • f.hom.range from (one_leftCoset _).symm] at r
  rw [leftCoset_eq_iff, mul_one] at r
  exact hb (inv_inv b ▸ Subgroup.inv_mem _ r)

end

section

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem g_apply_fromCoset (x : B) (y : X) :
    GrpCat.SurjectiveOfEpiAuxs.g x (fromCoset y) = fromCoset ⟨x • ↑y,
      by obtain ⟨z, hz⟩ := y.2; exact ⟨x * z, by simp [← hz, smul_smul]⟩⟩ := rfl

end

section

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem g_ne_h (x : B) (hx : x ∉ f.hom.range) : GrpCat.SurjectiveOfEpiAuxs.g ≠ GrpCat.SurjectiveOfEpiAuxs.h := by
  intro r
  apply GrpCat.SurjectiveOfEpiAuxs.fromCoset_ne_of_nin_range _ hx
  replace r :=
    DFunLike.congr_fun (DFunLike.congr_fun r x) (fromCoset ⟨f.hom.range, ⟨1, one_leftCoset _⟩⟩)
  simpa [GrpCat.SurjectiveOfEpiAuxs.g_apply_fromCoset, «GrpCat.SurjectiveOfEpiAuxs.h», GrpCat.SurjectiveOfEpiAuxs.tau, GrpCat.SurjectiveOfEpiAuxs.g_apply_infinity] using r

end

section

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem h_apply_fromCoset' (x : B) (b : B) (hb : b ∈ f.hom.range) :
    GrpCat.SurjectiveOfEpiAuxs.h x (fromCoset ⟨b • f.hom.range, b, rfl⟩) = fromCoset ⟨b • ↑f.hom.range, b, rfl⟩ := (GrpCat.SurjectiveOfEpiAuxs.fromCoset_eq_of_mem_range _ hb).symm ▸ GrpCat.SurjectiveOfEpiAuxs.h_apply_fromCoset f x

end

section

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem h_apply_fromCoset (x : B) :
    (GrpCat.SurjectiveOfEpiAuxs.h x) (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) =
      fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩ := by
  change ((τ).symm.trans (GrpCat.SurjectiveOfEpiAuxs.g x)).trans τ _ = _
  simp [-MonoidHom.coe_range, GrpCat.SurjectiveOfEpiAuxs.τ_symm_apply_fromCoset, GrpCat.SurjectiveOfEpiAuxs.g_apply_infinity, GrpCat.SurjectiveOfEpiAuxs.τ_apply_infinity]

end

section

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem h_apply_fromCoset_nin_range (x : B) (hx : x ∈ f.hom.range) (b : B) (hb : b ∉ f.hom.range) :
    GrpCat.SurjectiveOfEpiAuxs.h x (fromCoset ⟨b • f.hom.range, b, rfl⟩) = fromCoset ⟨(x * b) • ↑f.hom.range, x * b, rfl⟩ := by
  change ((τ).symm.trans (GrpCat.SurjectiveOfEpiAuxs.g x)).trans τ _ = _
  simp only [GrpCat.SurjectiveOfEpiAuxs.tau, Equiv.coe_trans, Function.comp_apply]
  rw [Equiv.symm_swap,
    @Equiv.swap_apply_of_ne_of_ne X' _ (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) ∞
      (fromCoset ⟨b • ↑f.hom.range, b, rfl⟩) (GrpCat.SurjectiveOfEpiAuxs.fromCoset_ne_of_nin_range _ hb) (by simp)]
  simp only [GrpCat.SurjectiveOfEpiAuxs.g_apply_fromCoset, leftCoset_assoc]
  refine Equiv.swap_apply_of_ne_of_ne (GrpCat.SurjectiveOfEpiAuxs.fromCoset_ne_of_nin_range _ fun r => hb ?_) (by simp)
  convert Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) r
  rw [← mul_assoc, inv_mul_cancel, one_mul]

end

section

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem h_apply_infinity (x : B) (hx : x ∈ f.hom.range) : (GrpCat.SurjectiveOfEpiAuxs.h x) ∞ = ∞ := by
  change ((τ).symm.trans (GrpCat.SurjectiveOfEpiAuxs.g x)).trans τ _ = _
  simp only [Equiv.coe_trans, Function.comp_apply]
  rw [GrpCat.SurjectiveOfEpiAuxs.τ_symm_apply_infinity, GrpCat.SurjectiveOfEpiAuxs.g_apply_fromCoset]
  simpa only using GrpCat.SurjectiveOfEpiAuxs.τ_apply_fromCoset' f x hx

end

section

open scoped Pointwise

variable {A : Type u} {B : Type v}

variable [Group A] [Group B]

theorem ker_eq_bot_of_cancel {f : A →* B} (h : ∀ u v : f.ker →* A, f.comp u = f.comp v → u = v) :
    f.ker = ⊥ := by simpa using congr_arg range (h f.ker.subtype 1 (by cat_disch))

end

section

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem mul_smul (b b' : B) (x : X') : (b * b') • x = b • b' • x := match x with
  | fromCoset y => by
    change fromCoset _ = fromCoset _
    simp only [leftCoset_assoc]
  | ∞ => rfl

end

section

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem one_smul (x : X') : (1 : B) • x = x := match x with
  | fromCoset y => by
    change fromCoset _ = fromCoset _
    simp only [one_leftCoset]
  | ∞ => rfl

end

section

open scoped Pointwise

variable {A : Type u} {B : Type v}

variable [CommGroup A] [CommGroup B]

theorem range_eq_top_of_cancel {f : A →* B}
    (h : ∀ u v : B →* B ⧸ f.range, u.comp f = v.comp f → u = v) : f.range = ⊤ := by
  specialize h 1 (QuotientGroup.mk' _) _
  · ext1 x
    simp only [one_apply, coe_comp, coe_mk', Function.comp_apply]
    rw [show (1 : B ⧸ f.range) = (1 : B) from QuotientGroup.mk_one _, QuotientGroup.eq, inv_one,
      one_mul]
    exact ⟨x, rfl⟩
  replace h : (QuotientGroup.mk' f.range).ker = (1 : B →* B ⧸ f.range).ker := by rw [h]
  rwa [ker_one, QuotientGroup.ker_mk'] at h

end

section

open scoped Pointwise

variable {A B : CommGrpCat.{u}} (f : A ⟶ B)

theorem range_eq_top_of_epi [Epi f] : f.hom.range = ⊤ := MonoidHom.range_eq_top_of_cancel fun u v GrpCat.SurjectiveOfEpiAuxs.h => ConcreteCategory.ext_iff.mp <|
    (@cancel_epi _ _ _ _ _ f _ (ofHom u) (ofHom v)).1 (ConcreteCategory.ext GrpCat.SurjectiveOfEpiAuxs.h)

end

section

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem surjective_of_epi [Epi f] : Function.Surjective f := by
  dsimp [Function.Surjective]
  by_contra! ⟨b, hb⟩
  exact
    SurjectiveOfEpiAuxs.g_ne_h f b (fun ⟨c, hc⟩ => hb _ hc)
      (congr_arg GrpCat.Hom.hom ((cancel_epi f).1 (SurjectiveOfEpiAuxs.comp_eq f)))

end

section

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem τ_apply_fromCoset' (x : B) (hx : x ∈ f.hom.range) :
    τ (fromCoset ⟨x • ↑f.hom.range, ⟨x, rfl⟩⟩) = ∞ := (GrpCat.SurjectiveOfEpiAuxs.fromCoset_eq_of_mem_range _ hx).symm ▸ GrpCat.SurjectiveOfEpiAuxs.τ_apply_fromCoset _

end

section

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem τ_symm_apply_fromCoset :
    Equiv.symm τ (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) = ∞ := by
  rw [GrpCat.SurjectiveOfEpiAuxs.tau, Equiv.symm_swap, Equiv.swap_apply_left]

end

section

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem τ_symm_apply_infinity :
    Equiv.symm τ ∞ = fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩ := by
  rw [GrpCat.SurjectiveOfEpiAuxs.tau, Equiv.symm_swap, Equiv.swap_apply_right]

end
