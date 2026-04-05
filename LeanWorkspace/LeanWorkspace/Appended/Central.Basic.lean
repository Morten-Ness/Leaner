import Mathlib

section

variable (K : Type u) [CommSemiring K] (D D' : Type v) [Semiring D] [Algebra K D]
  [h : IsCentral K D] [Semiring D'] [Algebra K D']

theorem baseField_essentially_unique
    (k K D : Type*) [Field k] [Field K] [Ring D] [Nontrivial D]
    [Algebra k K] [Algebra K D] [Algebra k D] [IsScalarTower k K D]
    [Algebra.IsCentral k D] :
    Function.Bijective (algebraMap k K) := by
  haveI : Algebra.IsCentral K D :=
  { out := fun x ↦ show x ∈ Subalgebra.center k D → _ by
      simp only [Algebra.IsCentral.center_eq_bot, mem_bot, Set.mem_range, forall_exists_index]
      rintro x rfl
      exact ⟨algebraMap k K x, by simp [algebraMap_eq_smul_one, smul_assoc]⟩ }
  refine ⟨FaithfulSMul.algebraMap_injective k K, fun x => ?_⟩
  have H : algebraMap K D x ∈ (Subalgebra.center K D : Set D) := Subalgebra.algebraMap_mem _ _
  rw [show (Subalgebra.center K D : Set D) = Subalgebra.center k D by rfl] at H
  simp only [Algebra.IsCentral.center_eq_bot, coe_bot, Set.mem_range] at H
  obtain ⟨x', H⟩ := H
  exact ⟨x', (algebraMap K D).injective <| by simp [← H, algebraMap_eq_smul_one]⟩

end

section

variable (K : Type u) [CommSemiring K] (D D' : Type v) [Semiring D] [Algebra K D]
  [h : IsCentral K D] [Semiring D'] [Algebra K D']

theorem mem_center_iff {x : D} : x ∈ Subalgebra.center K D ↔ ∃ (a : K), x = algebraMap K D a := by
  rw [Algebra.IsCentral.center_eq_bot, Algebra.mem_bot]
  simp [eq_comm]

end

section

variable (K : Type u) [CommSemiring K] (D D' : Type v) [Semiring D] [Algebra K D]
  [h : IsCentral K D] [Semiring D'] [Algebra K D']

theorem of_algEquiv (e : D ≃ₐ[K] D') : Algebra.IsCentral K D' where
  out x hx := have ⟨k, hk⟩ := h.1 ((MulEquivClass.apply_mem_center_iff e.symm).mpr hx)
    ⟨k, by simpa [ofId] using congr(e $hk)⟩

end
