import Mathlib

section

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem inv_mem_resolventSet {r : Rˣ} {a : Aˣ} (h : (r : R) ∈ resolventSet R (a : A)) :
    (↑r⁻¹ : R) ∈ resolventSet R (↑a⁻¹ : A) := by
  rw [spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one, ← Units.smul_def] at h ⊢
  rw [IsUnit.smul_sub_iff_sub_inv_smul, inv_inv, IsUnit.sub_iff]
  have h₁ : (a : A) * (r • (↑a⁻¹ : A) - 1) = r • (1 : A) - a := by
    rw [mul_sub, mul_smul_comm, a.mul_inv, mul_one]
  have h₂ : (r • (↑a⁻¹ : A) - 1) * a = r • (1 : A) - a := by
    rw [sub_mul, smul_mul_assoc, a.inv_mul, one_mul]
  have hcomm : Commute (a : A) (r • (↑a⁻¹ : A) - 1) := by rwa [← h₂] at h₁
  exact (hcomm.isUnit_mul_iff.mp (h₁.symm ▸ h)).2

end

section

open scoped Pointwise Ring

variable {R : Type u} {A : Type v} [Semifield R] [Ring A] [Algebra R A]

theorem inv₀_mem_inv_iff {r : R} {a : Aˣ} :
    r⁻¹ ∈ spectrum R (↑a⁻¹ : A) ↔ r ∈ spectrum R (a : A) := by
  simp

alias ⟨of_inv₀_mem, inv₀_mem⟩ := spectrum.inv₀_mem_iff
alias ⟨of_inv₀_mem_inv, inv₀_mem_inv⟩ := inv₀_mem_inv_iff

end

section

open scoped Pointwise Ring

variable {F R A B : Type*} [CommSemiring R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

variable [FunLike F A B] [AlgHomClass F R A B]

theorem mem_resolventSet_apply (φ : F) {a : A} {r : R} (h : r ∈ resolventSet R a) :
    r ∈ resolventSet R ((φ : A → B) a) := by
  simpa only [map_sub, AlgHomClass.commutes] using h.map φ

end

section

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem of_subsingleton [Subsingleton A] (a : A) : spectrum R a = ∅ := by
  rw [spectrum, spectrum.resolventSet_of_subsingleton, Set.compl_univ]

end

section

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem resolventSet_of_subsingleton [Subsingleton A] (a : A) : resolventSet R a = Set.univ := by
  simp_rw [resolventSet, Subsingleton.elim (algebraMap R A _ - a) 1, isUnit_one, Set.setOf_true]

end

section

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

variable [InvolutiveStar R] [StarRing A] [StarModule R A]

theorem star_mem_resolventSet_iff {r : R} {a : A} :
    star r ∈ resolventSet R a ↔ r ∈ resolventSet R (star a) := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    simpa only [spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one, star_sub, star_smul,
      star_star, star_one] using IsUnit.star h

end

section

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem subset_singleton_zero_compl {a : A} (ha : IsUnit a) : spectrum R a ⊆ {0}ᶜ := Set.subset_compl_singleton_iff.mpr <| spectrum.zero_notMem R ha

end

section

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommRing R] [Ring A] [Algebra R A]

theorem subset_subalgebra {S R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]
    [SetLike S A] [SubringClass S A] [SMulMemClass S R A] {s : S} (a : s) :
    spectrum R (a : A) ⊆ spectrum R a := Set.compl_subset_compl.mpr fun _ ↦ IsUnit.map (SubalgebraClass.val s)

end

section

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem units_smul_resolvent {r : Rˣ} {s : R} {a : A} :
    r • resolvent a (s : R) = resolvent (r⁻¹ • a) (r⁻¹ • s : R) := by
  by_cases h : s ∈ spectrum R a
  · rw [spectrum.mem_iff] at h
    simp only [resolvent, Algebra.algebraMap_eq_smul_one] at *
    rw [smul_assoc, ← smul_sub]
    have h' : ¬IsUnit (r⁻¹ • (s • (1 : A) - a)) := fun hu =>
      h (by simpa only [smul_inv_smul] using IsUnit.smul r hu)
    simp only [Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ h', smul_zero]
  · simp only [resolvent]
    have h' : IsUnit (r • algebraMap R A (r⁻¹ • s) - a) := by
      simpa [Algebra.algebraMap_eq_smul_one, smul_assoc] using spectrum.notMem_iff.mp h
    rw [← h'.val_subInvSMul, ← (spectrum.notMem_iff.mp h).unit_spec, Ring.inverse_unit, Ring.inverse_unit,
      h'.val_inv_subInvSMul]
    simp only [Algebra.algebraMap_eq_smul_one, smul_assoc, smul_inv_smul]

end

section

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem units_smul_resolvent_self {r : Rˣ} {a : A} :
    r • resolvent a (r : R) = resolvent (r⁻¹ • a) (1 : R) := by
  simpa only [Units.smul_def, smul_eq_mul, Units.inv_mul] using
    @spectrum.units_smul_resolvent _ _ _ _ _ r r a

end

section

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem zero_mem_resolventSet_of_unit (a : Aˣ) : 0 ∈ resolventSet R (a : A) := by
  simpa only [spectrum.mem_resolventSet_iff, ← spectrum.notMem_iff, spectrum.zero_notMem_iff] using a.isUnit

end
