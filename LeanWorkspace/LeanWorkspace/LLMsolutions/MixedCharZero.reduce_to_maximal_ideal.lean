FAIL
import Mathlib

variable (R : Type*) [CommRing R]

theorem reduce_to_maximal_ideal {p : ℕ} (hp : Nat.Prime p) :
    (∃ I : Ideal R, I ≠ ⊤ ∧ CharP (R ⧸ I) p) ↔ ∃ I : Ideal R, I.IsMaximal ∧ CharP (R ⧸ I) p := by
  constructor
  · rintro ⟨I, hI, hchar⟩
    have hnontriv : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial hI
    let P : Ideal (R ⧸ I) := Ideal.span ({(p : R ⧸ I)} : Set (R ⧸ I))
    have hP_ne_top : P ≠ ⊤ := by
      intro htop
      have hpzero : (p : R ⧸ I) = 0 := by
        have hmem : (p : R ⧸ I) ∈ P := Ideal.subset_span (by simp)
        rw [htop] at hmem
        simpa using hmem
      have hdiv : p ∣ 0 := (CharP.cast_eq_zero_iff (R := R ⧸ I) p 0).mp hpzero
      exact hp.ne_zero (Nat.dvd_zero p)
    obtain ⟨M, hPM, hMmax⟩ := Ideal.exists_le_maximal P hP_ne_top
    have hMprime : M.IsPrime := hMmax.isPrime
    have hcharM : CharP ((R ⧸ I) ⧸ M) p := by
      exact Ideal.Quotient.charP_of_prime hMprime hp
    let f : R →+* (R ⧸ I) ⧸ M := (Ideal.Quotient.mk M).comp (Ideal.Quotient.mk I)
    let K : Ideal R := RingHom.ker f
    have hKmax : K.IsMaximal := by
      have hf_surj : Function.Surjective f := by
        intro x
        rcases Ideal.Quotient.mk_surjective M x with ⟨y, rfl⟩
        rcases Ideal.Quotient.mk_surjective I y with ⟨z, rfl⟩
        refine ⟨z, rfl⟩
      exact Ideal.isMaximal_of_isField_quotient_of_surjective f hf_surj inferInstance
    have hcharK : CharP (R ⧸ K) p := by
      let e : R ⧸ K ≃+* (R ⧸ I) ⧸ M := RingHom.quotientKerEquivOfSurjective f (by
        intro x
        rcases Ideal.Quotient.mk_surjective M x with ⟨y, rfl⟩
        rcases Ideal.Quotient.mk_surjective I y with ⟨z, rfl⟩
        refine ⟨z, rfl⟩)
      exact e.symm.toRingHom.charP_iff.mp hcharM
    exact ⟨K, hKmax, hcharK⟩
  · rintro ⟨I, hImax, hchar⟩
    exact ⟨I, hImax.ne_top, hchar⟩
