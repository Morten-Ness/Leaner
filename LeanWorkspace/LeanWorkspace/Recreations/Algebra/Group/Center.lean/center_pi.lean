import Mathlib

variable {M : Type*} {S T : Set M}

variable [Mul M]

theorem center_pi {ι : Type*} {A : ι → Type*} [Π i, Mul (A i)] :
    Set.center (Π i, A i) = univ.pi fun i ↦ Set.center (A i) := by
  classical
  ext x
  simp only [mem_pi, Set.mem_center_iff, isMulCentral_iff, mem_univ, forall_true_left,
    commute_iff_eq, funext_iff, Pi.mul_def]
  refine ⟨fun ⟨h1, h2, h3⟩ i ↦ ?_, by grind⟩
  exact ⟨fun a ↦ by simpa using h1 (Function.update x i a) i,
    fun b c ↦ by simpa using h2 (Function.update x i b) (Function.update x i c) i,
    fun a b ↦ by simpa using h3 (Function.update x i a) (Function.update x i b) i⟩

