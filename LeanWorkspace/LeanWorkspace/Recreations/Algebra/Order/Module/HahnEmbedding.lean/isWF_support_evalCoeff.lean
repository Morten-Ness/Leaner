import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

set_option backward.isDefEq.respectTransparency false in
theorem isWF_support_evalCoeff [IsOrderedAddMonoid R] [Archimedean R] (x : M) :
    (HahnEmbedding.Partial.evalCoeff f x).support.IsWF := by
  rw [Set.isWF_iff_no_descending_seq]
  by_contra! ⟨seq, ⟨hanti, hmem⟩⟩
  have hnonempty : ∃ y : f.val.domain, y.val - x ∈ ball K (seq 0) := by
    specialize hmem 0
    contrapose hmem with hempty
    simp [HahnEmbedding.Partial.evalCoeff, dif_neg hempty]
  obtain ⟨y, hy⟩ := hnonempty
  have hmem' (n : ℕ) : seq n ∈ (ofLex (f.val y)).coeff.support := by
    specialize hmem n
    rw [Function.mem_support] at ⊢ hmem
    convert hmem using 1
    refine (HahnEmbedding.Partial.evalCoeff_eq f ((ball_strictAnti K).antitone ?_ hy)).symm
    simpa using hanti.antitone (show 0 ≤ n by simp)
  obtain hwf := (ofLex (f.val y)).isWF_support
  contrapose! hwf
  rw [Set.isWF_iff_no_descending_seq]
  simpa using ⟨seq, hanti, hmem'⟩

