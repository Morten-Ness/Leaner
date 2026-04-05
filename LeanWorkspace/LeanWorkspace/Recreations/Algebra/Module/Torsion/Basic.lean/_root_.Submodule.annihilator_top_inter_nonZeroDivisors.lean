import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

theorem _root_.Submodule.annihilator_top_inter_nonZeroDivisors [Module.Finite R M]
    (hM : Module.IsTorsion R M) : ((⊤ : Submodule R M).annihilator ∩ R⁰ : Set R).Nonempty := by
  obtain ⟨S, hS⟩ := ‹Module.Finite R M›.fg_top
  refine ⟨_, ?_, (∏ x ∈ S, (@hM x).choose : R⁰).prop⟩
  rw [Submonoid.coe_finset_prod, SetLike.mem_coe, ← hS, mem_annihilator_span]
  intro n
  letI := Classical.decEq M
  rw [← Finset.prod_erase_mul _ _ n.prop, mul_smul, ← Submonoid.smul_def, (@hM n).choose_spec,
    smul_zero]

