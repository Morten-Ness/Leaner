import Mathlib

section

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem AddSubmonoidClass.IsHomogeneous.ext
    {ℳ : ι → σ} [Decomposition ℳ] {P : Type*} [SetLike P M] [AddSubmonoidClass P M]
    {p q : P} (hp : DirectSum.SetLike.IsHomogeneous ℳ p) (hq : DirectSum.SetLike.IsHomogeneous ℳ q)
    (hpq : ∀ i, ∀ m ∈ ℳ i, m ∈ p ↔ m ∈ q) :
    p = q := by
  refine SetLike.ext fun m ↦ ?_
  rw [DirectSum.AddSubmonoidClass.IsHomogeneous.mem_iff ℳ p hp,
    DirectSum.AddSubmonoidClass.IsHomogeneous.mem_iff ℳ q hq]
  exact forall_congr' fun i ↦ hpq i _ (DirectSum.decompose ℳ _ i).2

end

section

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem AddSubmonoidClass.IsHomogeneous.mem_iff
    {P : Type*} [SetLike P M] [AddSubmonoidClass P M] (p : P)
    (hp : DirectSum.SetLike.IsHomogeneous ℳ p) {x} :
    x ∈ p ↔ ∀ i, (DirectSum.decompose ℳ x i : M) ∈ p := by
  classical
  refine ⟨fun hx i ↦ hp i hx, fun hx ↦ ?_⟩
  rw [← DirectSum.sum_support_decompose ℳ x]
  exact sum_mem (fun i _ ↦ hx i)

end

section

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem Decomposition.inductionOn {motive : M → Prop} (zero : motive 0)
    (homogeneous : ∀ {i} (m : ℳ i), motive (m : M))
    (add : ∀ m m' : M, motive m → motive m' → motive (m + m')) : ∀ m, motive m := by
  let ℳ' : ι → AddSubmonoid M := fun i ↦
    (⟨⟨ℳ i, fun x y ↦ AddMemClass.add_mem x y⟩, (ZeroMemClass.zero_mem _)⟩ : AddSubmonoid M)
  haveI t : DirectSum.Decomposition ℳ' :=
    { decompose' := DirectSum.decompose ℳ
      left_inv := fun _ ↦ (DirectSum.decompose ℳ).left_inv _
      right_inv := fun _ ↦ (DirectSum.decompose ℳ).right_inv _ }
  have mem : ∀ m, m ∈ iSup ℳ' := fun _m ↦
    (DirectSum.IsInternal.addSubmonoid_iSup_eq_top ℳ' (DirectSum.Decomposition.isInternal ℳ')).symm ▸ trivial
  -- Porting note: needs to use @ even though no implicit argument is provided
  exact fun m ↦ @AddSubmonoid.iSup_induction _ _ _ ℳ' _ _ (mem m)
    (fun i m h ↦ homogeneous ⟨m, h⟩) zero add
--  exact fun m ↦
--    AddSubmonoid.iSup_induction ℳ' (mem m) (fun i m h ↦ h_homogeneous ⟨m, h⟩) h_zero h_add

end

section

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem Decomposition.isInternal : DirectSum.IsInternal ℳ := ⟨Decomposition.right_inv.injective, Decomposition.left_inv.surjective⟩

end

section

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem decompose_add (x y : M) : DirectSum.decompose ℳ (x + y) = DirectSum.decompose ℳ x + DirectSum.decompose ℳ y := map_add (DirectSum.decomposeAddEquiv ℳ) x y

end

section

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem decompose_coe {i : ι} (x : ℳ i) : DirectSum.decompose ℳ (x : M) = DirectSum.of _ i x := by
  rw [← DirectSum.decompose_symm_of _, Equiv.apply_symm_apply]

end

section

open scoped DirectSum

variable {ι R M σ : Type*}

variable [DecidableEq ι] [Semiring R] [AddCommMonoid M] [Module R M]

variable (ℳ : ι → Submodule R M)

variable [Decomposition ℳ]

theorem decompose_lhom_ext {N} [AddCommMonoid N] [Module R N] ⦃f g : M →ₗ[R] N⦄
    (h : ∀ i, f ∘ₗ (ℳ i).subtype = g ∘ₗ (ℳ i).subtype) : f = g := LinearMap.ext <| (DirectSum.decomposeLinearEquiv ℳ).symm.surjective.forall.mpr <|
    suffices f ∘ₗ (DirectSum.decomposeLinearEquiv ℳ).symm
           = (g ∘ₗ (DirectSum.decomposeLinearEquiv ℳ).symm : (⨁ i, ℳ i) →ₗ[R] N) from
      DFunLike.congr_fun this
    linearMap_ext _ fun i => by
      simp_rw [LinearMap.comp_assoc, decomposeLinearEquiv_symm_comp_lof ℳ i, h]

end

section

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommGroup M]

variable [SetLike σ M] [AddSubgroupClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem decompose_neg (x : M) : DirectSum.decompose ℳ (-x) = -DirectSum.decompose ℳ x := map_neg (DirectSum.decomposeAddEquiv ℳ) x

end

section

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem decompose_of_mem_ne {x : M} {i j : ι} (hx : x ∈ ℳ i) (hij : i ≠ j) :
    (DirectSum.decompose ℳ x j : M) = 0 := by
  rw [DirectSum.decompose_of_mem _ hx, DirectSum.of_eq_of_ne _ _ _ hij.symm, ZeroMemClass.coe_zero]

end

section

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem decompose_of_mem_same {x : M} {i : ι} (hx : x ∈ ℳ i) : (DirectSum.decompose ℳ x i : M) = x := by
  rw [DirectSum.decompose_of_mem _ hx, DirectSum.of_eq_same, Subtype.coe_mk]

end

section

variable {ι R M σ : Type*}

variable [DecidableEq ι] [Semiring R] [AddCommMonoid M] [Module R M]

variable (ℳ : ι → Submodule R M)

variable [Decomposition ℳ]

theorem decompose_smul (r : R) (x : M) : DirectSum.decompose ℳ (r • x) = r • DirectSum.decompose ℳ x := map_smul (DirectSum.decomposeLinearEquiv ℳ) r x

end

section

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommGroup M]

variable [SetLike σ M] [AddSubgroupClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem decompose_sub (x y : M) : DirectSum.decompose ℳ (x - y) = DirectSum.decompose ℳ x - DirectSum.decompose ℳ y := map_sub (DirectSum.decomposeAddEquiv ℳ) x y

end

section

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem decompose_sum {ι'} (s : Finset ι') (f : ι' → M) :
    DirectSum.decompose ℳ (∑ i ∈ s, f i) = ∑ i ∈ s, DirectSum.decompose ℳ (f i) := map_sum (DirectSum.decomposeAddEquiv ℳ) f s

end

section

open scoped DirectSum

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem decompose_symm_add (x y : ⨁ i, ℳ i) :
    (DirectSum.decompose ℳ).symm (x + y) = (DirectSum.decompose ℳ).symm x + (DirectSum.decompose ℳ).symm y := map_add (DirectSum.decomposeAddEquiv ℳ).symm x y

end

section

open scoped DirectSum

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommGroup M]

variable [SetLike σ M] [AddSubgroupClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem decompose_symm_neg (x : ⨁ i, ℳ i) : (DirectSum.decompose ℳ).symm (-x) = -(DirectSum.decompose ℳ).symm x := map_neg (DirectSum.decomposeAddEquiv ℳ).symm x

end

section

open scoped DirectSum

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommGroup M]

variable [SetLike σ M] [AddSubgroupClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem decompose_symm_sub (x y : ⨁ i, ℳ i) :
    (DirectSum.decompose ℳ).symm (x - y) = (DirectSum.decompose ℳ).symm x - (DirectSum.decompose ℳ).symm y := map_sub (DirectSum.decomposeAddEquiv ℳ).symm x y

end

section

open scoped DirectSum

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem decompose_symm_sum {ι'} (s : Finset ι') (f : ι' → ⨁ i, ℳ i) :
    (DirectSum.decompose ℳ).symm (∑ i ∈ s, f i) = ∑ i ∈ s, (DirectSum.decompose ℳ).symm (f i) := map_sum (DirectSum.decomposeAddEquiv ℳ).symm f s

end

section

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem decompose_symm_zero : (DirectSum.decompose ℳ).symm 0 = (0 : M) := map_zero (DirectSum.decomposeAddEquiv ℳ).symm

end

section

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem decompose_zero : DirectSum.decompose ℳ (0 : M) = 0 := map_zero (DirectSum.decomposeAddEquiv ℳ)

end

section

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem degree_eq_of_mem_mem {x : M} {i j : ι} (hxi : x ∈ ℳ i) (hxj : x ∈ ℳ j) (hx : x ≠ 0) :
    i = j := by
  contrapose! hx; rw [← DirectSum.decompose_of_mem_same ℳ hxj, DirectSum.decompose_of_mem_ne ℳ hxi hx]

end

section

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem sum_support_decompose [∀ (i) (x : ℳ i), Decidable (x ≠ 0)] (r : M) :
    (∑ i ∈ (DirectSum.decompose ℳ r).support, (DirectSum.decompose ℳ r i : M)) = r := by
  conv_rhs =>
    rw [← (DirectSum.decompose ℳ).symm_apply_apply r, ← sum_support_of (DirectSum.decompose ℳ r)]
  rw [DirectSum.decompose_symm_sum]
  simp_rw [DirectSum.decompose_symm_of]

end
