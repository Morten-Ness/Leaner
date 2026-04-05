import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

variable [Balanced C]

theorem exact_and_mono_f_iff_f_is_kernel [S.HasHomology] :
    S.Exact ∧ Mono S.f ↔ Nonempty (IsLimit (KernelFork.ofι S.f S.zero)) := by
  constructor
  · intro ⟨hS, _⟩
    exact ⟨hS.fIsKernel⟩
  · intro ⟨hS⟩
    exact ⟨S.exact_of_f_is_kernel hS, mono_of_isLimit_fork hS⟩

