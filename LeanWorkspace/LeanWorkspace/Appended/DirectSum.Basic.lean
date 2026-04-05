import Mathlib

section

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

theorem IsInternal.addSubmonoid_iSup_eq_top {M : Type*} [DecidableEq ι] [AddCommMonoid M]
    (A : ι → AddSubmonoid M) (h : DirectSum.IsInternal A) : iSup A = ⊤ := by
  rw [AddSubmonoid.iSup_eq_mrange_dfinsuppSumAddHom, AddMonoidHom.mrange_eq_top]
  exact Function.Bijective.surjective h

end

section

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

theorem coeAddMonoidHom_eq_dfinsuppSum [DecidableEq ι]
    {M S : Type*} [DecidableEq M] [AddCommMonoid M]
    [SetLike S M] [AddSubmonoidClass S M] (A : ι → S) (x : DirectSum ι fun i => A i) :
    DirectSum.coeAddMonoidHom A x = DFinsupp.sum x fun i => (fun x : A i => ↑x) := by
  simp only [DirectSum.coeAddMonoidHom, DirectSum.toAddMonoid, DFinsupp.liftAddHom, AddEquiv.coe_mk,
    Equiv.coe_fn_mk]
  exact DFinsupp.sumAddHom_apply _ x

end

section

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

theorem coe_of_apply {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] {A : ι → S} (i j : ι) (x : A i) :
    (DirectSum.of (fun i ↦ {x // x ∈ A i}) i x j : M) = if i = j then x else 0 := by
  obtain rfl | h := Decidable.eq_or_ne j i
  · rw [DirectSum.of_eq_same, if_pos rfl]
  · rw [DirectSum.of_eq_of_ne _ _ _ h, if_neg h.symm, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero]

end

section

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable [DecidableEq ι]

variable {γ : Type u₁} [AddCommMonoid γ]

theorem fromAddMonoid_of (i : ι) (f : γ →+ β i) : DirectSum.fromAddMonoid (DirectSum.of _ i f) = (DirectSum.of _ i).comp f := by
  rw [DirectSum.fromAddMonoid, DirectSum.toAddMonoid_of]
  rfl

end

section

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable [DecidableEq ι]

variable {γ : Type u₁} [AddCommMonoid γ]

theorem fromAddMonoid_of_apply (i : ι) (f : γ →+ β i) (x : γ) :
    DirectSum.fromAddMonoid (DirectSum.of _ i f) x = DirectSum.of _ i (f x) := by
      rw [DirectSum.fromAddMonoid_of, AddMonoidHom.coe_comp, Function.comp]

end

section

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable {M S : Type*} [AddCommMonoid M] [SetLike S M] [AddSubmonoidClass S M]

theorem hasFiniteSupport (A : ι → S) (x : DirectSum ι fun i => A i) :
    (fun i => (x i : M)).HasFiniteSupport := by
  classical
  exact (DFinsupp.support x).finite_toSet.subset (DirectSum.support_subset _ x)

end

section

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable {M S : Type*} [AddCommMonoid M] [SetLike S M] [AddSubmonoidClass S M]

variable {ι : Type*} {α : ι → Type*} {β : ι → Type*} [∀ i, AddCommMonoid (α i)]

variable [∀ i, AddCommMonoid (β i)] (f : ∀ (i : ι), α i →+ β i)

theorem map_injective : Function.Injective (DirectSum.map f) ↔ ∀ i, Function.Injective (f i) := by
  classical exact DFinsupp.mapRange_injective (hf := fun _ ↦ map_zero _)

end

section

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable {M S : Type*} [AddCommMonoid M] [SetLike S M] [AddSubmonoidClass S M]

variable {ι : Type*} {α : ι → Type*} {β : ι → Type*} [∀ i, AddCommMonoid (α i)]

variable [∀ i, AddCommMonoid (β i)] (f : ∀ (i : ι), α i →+ β i)

theorem map_surjective : Function.Surjective (DirectSum.map f) ↔ (∀ i, Function.Surjective (f i)) := by
  classical exact DFinsupp.mapRange_surjective (hf := fun _ ↦ map_zero _)

end

section

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable {M S : Type*} [AddCommMonoid M] [SetLike S M] [AddSubmonoidClass S M]

theorem support_subset [DecidableEq ι] [DecidableEq M] (A : ι → S) (x : DirectSum ι fun i => A i) :
    (Function.support fun i => (x i : M)) ⊆ ↑(DFinsupp.support x) := by
  intro m
  simp only [Function.mem_support, Finset.mem_coe, DFinsupp.mem_support_toFun, not_imp_not,
    ZeroMemClass.coe_eq_zero, imp_self]

end
