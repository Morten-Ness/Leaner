import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem totalDegree_rename_le (f : σ → τ) (p : MvPolynomial σ R) :
    (rename f p).totalDegree ≤ p.totalDegree := Finset.sup_le fun b => by
    classical
    intro h
    rw [rename_eq] at h
    have h' := Finsupp.mapDomain_support h
    rw [Finset.mem_image] at h'
    rcases h' with ⟨s, hs, rfl⟩
    exact (sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)).trans_le (MvPolynomial.le_totalDegree hs)

