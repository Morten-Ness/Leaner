import Mathlib

variable {R : Type*} [CommSemiring R] {S : Submonoid R} {M : Type*} [AddCommMonoid M]
  [Module R M] {M' : Type*} [AddCommMonoid M'] [Module R M'] (f : M →ₗ[R] M')

variable [IsLocalizedModule S f]

set_option backward.isDefEq.respectTransparency false in
theorem smul_mem_finsetIntegerMultiple_span [DecidableEq M] (x : M) (s : Finset M')
    (hx : f x ∈ Submodule.span R s) :
    ∃ (m : S), m • x ∈ Submodule.span R (IsLocalizedModule.finsetIntegerMultiple S f s) := by
  let y : S := IsLocalizedModule.commonDenomOfFinset S f s
  have hx₁ : y • (s : Set M') = f '' _ :=
    (IsLocalizedModule.finsetIntegerMultiple_image S f s).symm
  apply congrArg (Submodule.span R) at hx₁
  rw [Submodule.span_smul] at hx₁
  replace hx : _ ∈ y • Submodule.span R (s : Set M') := Set.smul_mem_smul_set hx
  rw [hx₁, ← f.map_smul, ← Submodule.map_span f] at hx
  obtain ⟨x', hx', hx''⟩ := hx
  obtain ⟨a, ha⟩ := (IsLocalizedModule.eq_iff_exists S f).mp hx''
  use a * y
  convert (Submodule.span R
    (IsLocalizedModule.finsetIntegerMultiple S f s : Set M)).smul_mem
      a hx' using 1
  convert ha.symm using 1
  simp only [Submonoid.smul_def, ← smul_smul]

