import Mathlib

variable {ι μ μ' : Type*}

variable [DecidableEq ι] [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {s : Finset ι}
  {n : μ} {f : ι →₀ μ}

theorem finsuppAntidiag_mono {s t : Finset ι} (h : s ⊆ t) (n : μ) :
    Finset.finsuppAntidiag s n ⊆ Finset.finsuppAntidiag t n := by
  intro a
  simp_rw [Finset.mem_finsuppAntidiag']
  rintro ⟨hsum, hmem⟩
  exact ⟨hsum, hmem.trans h⟩

