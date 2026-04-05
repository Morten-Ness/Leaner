FAIL
import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

theorem IsInternal.addSubmonoid_iSup_eq_top {M : Type*} [DecidableEq ι] [AddCommMonoid M]
    (A : ι → AddSubmonoid M) (h : DirectSum.IsInternal A) : iSup A = ⊤ := by
  refine top_unique ?_
  intro x hx
  let y := h.subtypeEquiv.symm x
  change x ∈ iSup A
  rw [← h.subtypeEquiv.apply_symm_apply x]
  clear hx x
  refine DirectSum.induction_on y ?_ ?_ ?_
  · simp [y]
  · intro i xi
    rw [AddSubmonoid.mem_iSup]
    exact ⟨i, xi.2⟩
  · intro a b ha hb
    exact (iSup A).add_mem ha hb
