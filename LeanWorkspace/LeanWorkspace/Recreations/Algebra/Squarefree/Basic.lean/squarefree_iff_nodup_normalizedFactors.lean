import Mathlib

variable {R : Type*}

variable [CommMonoidWithZero R] [UniqueFactorizationMonoid R]

theorem squarefree_iff_nodup_normalizedFactors [NormalizationMonoid R] {x : R}
    (x0 : x ≠ 0) : Squarefree x ↔ Multiset.Nodup (normalizedFactors x) := by
  classical
  rw [squarefree_iff_emultiplicity_le_one, Multiset.nodup_iff_count_le_one]
  haveI := nontrivial_of_ne x 0 x0
  constructor <;> intro h a
  · by_cases hmem : a ∈ normalizedFactors x
    · have ha := irreducible_of_normalized_factor _ hmem
      rcases h a with (h | h)
      · rw [← normalize_normalized_factor _ hmem]
        rw [emultiplicity_eq_count_normalizedFactors ha x0] at h
        assumption_mod_cast
      · have := ha.1
        contradiction
    · simp [Multiset.count_eq_zero_of_notMem hmem]
  · rw [or_iff_not_imp_right]
    intro hu
    rcases eq_or_ne a 0 with rfl | h0
    · simp [x0]
    rcases WfDvdMonoid.exists_irreducible_factor hu h0 with ⟨b, hib, hdvd⟩
    apply le_trans (emultiplicity_le_emultiplicity_of_dvd_left hdvd)
    rw [emultiplicity_eq_count_normalizedFactors hib x0]
    exact_mod_cast h (normalize b)

