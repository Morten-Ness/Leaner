FAIL
import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable {S : Subsemigroup M}

theorem subsingleton_of_subsingleton [Subsingleton (Subsemigroup M)] : Subsingleton M :=
by
  classical
  by_cases h : Nonempty M
  · rcases h with ⟨x⟩
    let T : Subsemigroup M :=
      Subsemigroup.closure ({x} : Set M)
    have hT : T = ⊤ := Subsingleton.elim _ _
    refine ⟨?_⟩
    intro y z
    have hyT : y ∈ T := by
      simpa [hT]
    have hzT : z ∈ T := by
      simpa [hT]
    exact Subsingleton.elim y z
  · refine ⟨?_⟩
    intro x
    exact (h ⟨x⟩).elim
