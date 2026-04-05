import Mathlib

section

variable {R M M' N N' P P' : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

theorem Exact.inl_snd : Function.Exact (LinearMap.inl R M N) (LinearMap.snd R M N) := by
  rintro ⟨x, y⟩
  simp only [LinearMap.snd_apply, @eq_comm _ y, LinearMap.coe_inl, Set.mem_range, Prod.mk.injEq,
    exists_eq_left]

end

section

variable {R M M' N N' P P' : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

theorem Exact.inr_fst : Function.Exact (LinearMap.inr R M N) (LinearMap.fst R M N) := by
  rintro ⟨x, y⟩
  simp only [LinearMap.fst_apply, @eq_comm _ x, LinearMap.coe_inr, Set.mem_range, Prod.mk.injEq,
    exists_eq_right]

end

section

variable {R M M' N N' P P' : Type*}

variable [Semiring R]

variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

theorem Exact.split_tfae' (h : Function.Exact f g) :
    List.TFAE [
      Function.Injective f ∧ ∃ l, g ∘ₗ l = LinearMap.id,
      Function.Surjective g ∧ ∃ l, l ∘ₗ f = LinearMap.id,
      ∃ e : N ≃ₗ[R] M × P, f = e.symm ∘ₗ LinearMap.inl R M P ∧ g = LinearMap.snd R M P ∘ₗ e] := by
  tfae_have 1 → 3
  | ⟨hf, l, hl⟩ => ⟨_, (h.splitSurjectiveEquiv hf ⟨l, hl⟩).2⟩
  tfae_have 2 → 3
  | ⟨hg, l, hl⟩ => ⟨_, (h.splitInjectiveEquiv hg ⟨l, hl⟩).2⟩
  tfae_have 3 → 1
  | ⟨e, e₁, e₂⟩ => by
    have : Function.Injective f := e₁ ▸ e.symm.injective.comp LinearMap.inl_injective
    exact ⟨this, ⟨_, ((h.splitSurjectiveEquiv this).symm ⟨e, e₁, e₂⟩).2⟩⟩
  tfae_have 3 → 2
  | ⟨e, e₁, e₂⟩ => by
    have : Function.Surjective g := e₂ ▸ Prod.snd_surjective.comp e.surjective
    exact ⟨this, ⟨_, ((h.splitInjectiveEquiv this).symm ⟨e, e₁, e₂⟩).2⟩⟩
  tfae_finish

end

section

variable {R M M' N N' P P' : Type*}

variable [Semiring R]

variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

theorem Exact.split_tfae
    {R M N P} [Semiring R] [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (h : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g) :
    List.TFAE [
      ∃ l, g ∘ₗ l = LinearMap.id,
      ∃ l, l ∘ₗ f = LinearMap.id,
      ∃ e : N ≃ₗ[R] M × P, f = e.symm ∘ₗ LinearMap.inl R M P ∧ g = LinearMap.snd R M P ∘ₗ e] := by
  tfae_have 1 ↔ 3 := by
    simpa using (h.splitSurjectiveEquiv hf).nonempty_congr
  tfae_have 2 ↔ 3 := by
    simpa using (h.splitInjectiveEquiv hg).nonempty_congr
  tfae_finish

end

section

variable {R M M' N N' P P' : Type*}

variable (f : M → N) (g : N → P) (g' : P → P')

theorem comp_injective [One P] [One P'] (mulExact : Function.MulExact f g)
    (inj : Function.Injective g') (h0 : g' 1 = 1) :
    Function.MulExact f (g' ∘ g) := by
  intro x
  refine ⟨fun H => mulExact x |>.mp <| inj <| h0 ▸ H, ?_⟩
  intro H
  rw [Function.comp_apply, mulExact x |>.mpr H, h0]

end

section

variable {R M M' N N' P P' : Type*}

variable [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P}

theorem exact_iff_of_surjective_of_bijective_of_injective
    {M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
    [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N₃]
    [Module R M₁] [Module R M₂] [Module R M₃]
    [Module R N₁] [Module R N₂] [Module R N₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (f' : N₁ →ₗ[R] N₂) (g' : N₂ →ₗ[R] N₃)
    (τ₁ : M₁ →ₗ[R] N₁) (τ₂ : M₂ →ₗ[R] N₂) (τ₃ : M₃ →ₗ[R] N₃)
    (comm₁₂ : f'.comp τ₁ = τ₂.comp f) (comm₂₃ : g'.comp τ₂ = τ₃.comp g)
    (h₁ : Function.Surjective τ₁) (h₂ : Function.Bijective τ₂) (h₃ : Function.Injective τ₃) :
    Function.Exact f g ↔ Function.Exact f' g' := AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
    f.toAddMonoidHom g.toAddMonoidHom f'.toAddMonoidHom g'.toAddMonoidHom
    τ₁.toAddMonoidHom τ₂.toAddMonoidHom τ₃.toAddMonoidHom
    (by ext; apply DFunLike.congr_fun comm₁₂) (by ext; apply DFunLike.congr_fun comm₂₃) h₁ h₂ h₃

end

section

variable {R M M' N N' P P' : Type*}

variable [Group M] [Group N] [Group P] {f : M →* N} {g : N →* P}

theorem iff_monoidHom_rangeRestrict :
    Function.MulExact f g ↔ Function.MulExact f.range.subtype g.rangeRestrict := Function.MulExact.iff_rangeFactorization (one_mem g.range)

end

section

variable {R M M' N N' P P' : Type*}

variable [Group M] [Group N] [Group P] {f : M →* N} {g : N →* P}

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Type*} [CommMonoid X₁] [CommMonoid X₂] [CommMonoid X₃]
  [CommMonoid Y₁] [CommMonoid Y₂] [CommMonoid Y₃]
  (e₁ : X₁ ≃* Y₁) (e₂ : X₂ ≃* Y₂) (e₃ : X₃ ≃* Y₃)
  {f₁₂ : X₁ →* X₂} {f₂₃ : X₂ →* X₃} {g₁₂ : Y₁ →* Y₂} {g₂₃ : Y₂ →* Y₃}

theorem iff_of_ladder_mulEquiv (comm₁₂ : g₁₂.comp e₁ = MonoidHom.comp e₂ f₁₂)
    (comm₂₃ : g₂₃.comp e₂ = MonoidHom.comp e₃ f₂₃) : Function.MulExact g₁₂ g₂₃ ↔ Function.MulExact f₁₂ f₂₃ := (MonoidHom.mulExact_iff_of_surjective_of_bijective_of_injective _ _ _ _ e₁ e₂ e₃ comm₁₂ comm₂₃
    e₁.surjective e₂.bijective e₃.injective).symm

end

section

variable {R M M' N N' P P' : Type*}

variable (f : M → N) (g : N → P) (g' : P → P')

theorem iff_rangeFactorization [One P] (hg : 1 ∈ Set.range g) :
    letI : One (Set.range g) := ⟨⟨1, hg⟩⟩
    Function.MulExact f g ↔ Function.MulExact ((↑) : Set.range f → N) (Set.rangeFactorization g) := by
  letI : One (Set.range g) := ⟨⟨1, hg⟩⟩
  have : ((1 : Set.range g) : P) = 1 := rfl
  simp [Function.MulExact, Set.rangeFactorization, Subtype.ext_iff, this]

end

section

variable {R M M' N N' P P' : Type*}

variable [Group M] [Group N] [Group P] {f : M →* N} {g : N →* P}

theorem mulExact_iff_of_surjective_of_bijective_of_injective
    {M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [CommMonoid M₁] [CommMonoid M₂] [CommMonoid M₃]
    [CommMonoid N₁] [CommMonoid N₂] [CommMonoid N₃]
    (f : M₁ →* M₂) (g : M₂ →* M₃) (f' : N₁ →* N₂) (g' : N₂ →* N₃)
    (τ₁ : M₁ →* N₁) (τ₂ : M₂ →* N₂) (τ₃ : M₃ →* N₃)
    (comm₁₂ : f'.comp τ₁ = τ₂.comp f)
    (comm₂₃ : g'.comp τ₂ = τ₃.comp g)
    (h₁ : Function.Surjective τ₁) (h₂ : Function.Bijective τ₂) (h₃ : Function.Injective τ₃) :
    Function.MulExact f g ↔ Function.MulExact f' g' := by
  replace comm₁₂ := DFunLike.congr_fun comm₁₂
  replace comm₂₃ := DFunLike.congr_fun comm₂₃
  dsimp at comm₁₂ comm₂₃
  constructor
  · intro h y₂
    obtain ⟨x₂, rfl⟩ := h₂.2 y₂
    constructor
    · intro hx₂
      obtain ⟨x₁, rfl⟩ := (h x₂).1 (h₃ (by simpa only [map_one, comm₂₃] using hx₂))
      exact ⟨τ₁ x₁, by simp only [comm₁₂]⟩
    · rintro ⟨y₁, hy₁⟩
      obtain ⟨x₁, rfl⟩ := h₁ y₁
      rw [comm₂₃, (h x₂).2 _, map_one]
      exact ⟨x₁, h₂.1 (by simpa only [comm₁₂] using hy₁)⟩
  · intro h x₂
    constructor
    · intro hx₂
      obtain ⟨y₁, hy₁⟩ := (h (τ₂ x₂)).1 (by simp only [comm₂₃, hx₂, map_one])
      obtain ⟨x₁, rfl⟩ := h₁ y₁
      exact ⟨x₁, h₂.1 (by simpa only [comm₁₂] using hy₁)⟩
    · rintro ⟨x₁, rfl⟩
      apply h₃
      simp only [← comm₁₂, ← comm₂₃, Function.MulExact.apply_apply_eq_one h (τ₁ x₁), map_one]

end

section

variable {R M M' N N' P P' : Type*}

variable (f : M → N) (g : N → P) (g' : P → P')

theorem of_comp_eq_one_of_ker_in_range [One P] (hc : g.comp f = 1)
    (hr : ∀ y, g y = 1 → y ∈ Set.range f) :
    Function.MulExact f g := fun y ↦ ⟨hr y, fun ⟨x, hx⟩ ↦ hx ▸ congrFun hc x⟩

end

section

variable {R M M' N N' P P' : Type*}

variable (f : M → N) (g : N → P) (g' : P → P')

theorem of_comp_of_mem_range [One P] (h1 : g ∘ f = 1)
    (h2 : ∀ x, g x = 1 → x ∈ Set.range f) : Function.MulExact f g := fun y => Iff.intro (h2 y) <|
    Exists.rec ((forall_apply_eq_imp_iff (p := (g · = 1))).mpr (congrFun h1) y)

end

section

variable {R M M' N N' P P' : Type*}

variable [Group M] [Group N] [Group P] {f : M →* N} {g : N →* P}

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Type*} [CommMonoid X₁] [CommMonoid X₂] [CommMonoid X₃]
  [CommMonoid Y₁] [CommMonoid Y₂] [CommMonoid Y₃]
  (e₁ : X₁ ≃* Y₁) (e₂ : X₂ ≃* Y₂) (e₃ : X₃ ≃* Y₃)
  {f₁₂ : X₁ →* X₂} {f₂₃ : X₂ →* X₃} {g₁₂ : Y₁ →* Y₂} {g₂₃ : Y₂ →* Y₃}

theorem of_ladder_mulEquiv_of_mulExact' (comm₁₂ : g₁₂.comp e₁ = MonoidHom.comp e₂ f₁₂)
    (comm₂₃ : g₂₃.comp e₂ = MonoidHom.comp e₃ f₂₃) (H : Function.MulExact g₁₂ g₂₃) : Function.MulExact f₁₂ f₂₃ := (Function.MulExact.iff_of_ladder_mulEquiv _ _ _ comm₁₂ comm₂₃).1 H

end

section

variable {R M M' N N' P P' : Type*}

variable [Group M] [Group N] [Group P] {f : M →* N} {g : N →* P}

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Type*} [CommMonoid X₁] [CommMonoid X₂] [CommMonoid X₃]
  [CommMonoid Y₁] [CommMonoid Y₂] [CommMonoid Y₃]
  (e₁ : X₁ ≃* Y₁) (e₂ : X₂ ≃* Y₂) (e₃ : X₃ ≃* Y₃)
  {f₁₂ : X₁ →* X₂} {f₂₃ : X₂ →* X₃} {g₁₂ : Y₁ →* Y₂} {g₂₃ : Y₂ →* Y₃}

theorem of_ladder_mulEquiv_of_mulExact (comm₁₂ : g₁₂.comp e₁ = MonoidHom.comp e₂ f₁₂)
    (comm₂₃ : g₂₃.comp e₂ = MonoidHom.comp e₃ f₂₃) (H : Function.MulExact f₁₂ f₂₃) : Function.MulExact g₁₂ g₂₃ := (Function.MulExact.iff_of_ladder_mulEquiv _ _ _ comm₁₂ comm₂₃).2 H

end

section

variable {R M M' N N' P P' : Type*}

variable (f : M → N) (g : N → P) (g' : P → P')

theorem rangeFactorization [One P] (h : Function.MulExact f g) (hg : 1 ∈ Set.range g) :
    letI : One (Set.range g) := ⟨⟨1, hg⟩⟩
    Function.MulExact ((↑) : Set.range f → N) (Set.rangeFactorization g) :=
  (Function.MulExact.iff_rangeFactorization hg).1 h

end
