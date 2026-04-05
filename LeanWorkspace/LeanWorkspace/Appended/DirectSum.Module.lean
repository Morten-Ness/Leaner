import Mathlib

section

open scoped DirectSum

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

theorem apply_eq_component (f : ⨁ i, M i) (i : ι) : f i = DirectSum.component R ι M i f := rfl

-- Note(kmill): `@[ext]` cannot prove `ext_iff` because `R` is not determined by `f` or `g`.
-- This is not useful as an `@[ext]` lemma as the `ext` tactic cannot infer `R`.

end

section

variable {R : Type u} [Semiring R]

variable {ι : Type v} [dec_ι : DecidableEq ι]

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable (A : ι → Submodule R M)

set_option backward.isDefEq.respectTransparency false in
theorem coeLinearMap_eq_dfinsuppSum [DecidableEq M] (x : DirectSum ι fun i => A i) :
    DirectSum.coeLinearMap A x = DFinsupp.sum x fun i => (fun x : A i => ↑x) := by
  simp only [DirectSum.coeLinearMap, DirectSum.toModule, DFinsupp.lsum, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [DFinsupp.sumAddHom_apply]
  simp only [LinearMap.toAddMonoidHom_coe, Submodule.coe_subtype]

end

section

open scoped DirectSum

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

theorem ext_component_iff {f g : ⨁ i, M i} :
    f = g ↔ ∀ i, DirectSum.component R ι M i f = DirectSum.component R ι M i g := ⟨fun h _ ↦ by rw [h], DirectSum.ext_component R⟩

end

section

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable {κ : Type*}

theorem lequivCongrLeft_symm_lof [DecidableEq ι] [DecidableEq κ] {h : ι ≃ κ}
    {k : κ} {x : M (h.symm k)} :
    (DirectSum.lequivCongrLeft R h).symm (DirectSum.lof R κ (fun k => M (h.symm k)) k x) = DirectSum.lof R ι M (h.symm k) x := by
  rw [LinearEquiv.symm_apply_eq]
  symm
  exact DirectSum.lequivCongrLeft_lof _ rfl _ _ rfl

end

section

open scoped DirectSum

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

theorem linearEquivFunOnFintype_symm_coe [Fintype ι] (f : ⨁ i, M i) :
    (DirectSum.linearEquivFunOnFintype R ι M).symm f = f := (DirectSum.linearEquivFunOnFintype R ι M).symm_apply_apply _

end

section

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable [DecidableEq ι]

theorem mk_smul (s : Finset ι) (c : R) (x) : DirectSum.mk M s (c • x) = c • DirectSum.mk M s x := (DirectSum.lmk R ι M s).map_smul c x

end

section

variable {R : Type u} [Semiring R]

variable {ι : Type v} [dec_ι : DecidableEq ι]

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable (A : ι → Submodule R M)

theorem range_coeLinearMap : LinearMap.range (DirectSum.coeLinearMap A) = ⨆ i, A i := (Submodule.iSup_eq_range_dfinsupp_lsum _).symm

end
