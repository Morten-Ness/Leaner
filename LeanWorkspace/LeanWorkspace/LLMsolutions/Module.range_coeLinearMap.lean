FAIL
import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v} [dec_ι : DecidableEq ι]

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable (A : ι → Submodule R M)

theorem range_coeLinearMap : LinearMap.range (DirectSum.coeLinearMap A) = ⨆ i, A i := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine DirectSum.induction_on y ?_ ?_ ?_
    · simp
    · intro i xi
      change ((DirectSum.coeLinearMap A) (DirectSum.lof R ι (fun i => A i) i xi)) ∈ ⨆ i, A i
      simp [DirectSum.coeLinearMap]
    · intro a b ha hb
      simpa using Submodule.add_mem (⨆ i, A i) ha hb
  · intro hx
    rw [Submodule.mem_iSup_of_directed]
    · rcases hx with ⟨s, hs, hx⟩
      induction s using Finset.induction_on with
      | empty =>
          simp at hx
          subst hx
          exact ⟨0, by simp [DirectSum.coeLinearMap]⟩
      | @insert i s his ih =>
          rw [Finset.mem_insert, forall_eq_or_imp] at hs
          rcases hs with ⟨hi, hs⟩
          rw [Submodule.mem_sup] at hx
          rcases hx with ⟨y, hy, z, hz, rfl⟩
          rcases ih hs hz with ⟨w, rfl⟩
          refine ⟨DirectSum.lof R ι (fun i => A i) i ⟨y, hi y hy⟩ + w, by simp [DirectSum.coeLinearMap]⟩
    · intro i j
      refine ⟨i ⊔ j, ?_, ?_⟩ <;> exact le_iSup (fun k => A k) _
