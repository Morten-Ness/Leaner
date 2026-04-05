import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable {M S : Type*} [AddCommMonoid M] [SetLike S M] [AddSubmonoidClass S M]

theorem support_subset [DecidableEq ι] [DecidableEq M] (A : ι → S) (x : DirectSum ι fun i => A i) :
    (Function.support fun i => (x i : M)) ⊆ ↑(DFinsupp.support x) := by
  intro m
  simp only [Function.mem_support, Finset.mem_coe, DFinsupp.mem_support_toFun, not_imp_not,
    ZeroMemClass.coe_eq_zero, imp_self]

