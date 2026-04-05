import Mathlib

variable {R : Type*} [CommRing R]

theorem quo_mul_pow_add_sum_rem_mul_pow_unique {g : R[X]} (hg : g.Monic) {n : ℕ}
    {q₁ q₂ : R[X]} {r₁ r₂ : Fin n → R[X]}
    (hr₁ : ∀ i, (r₁ i).degree < g.degree) (hr₂ : ∀ i, (r₂ i).degree < g.degree)
    (hf : q₁ * g ^ n + ∑ i, r₁ i * g ^ i.1 = q₂ * g ^ n + ∑ i, r₂ i * g ^ i.1) :
    q₁ = q₂ ∧ r₁ = r₂ := by
  induction n generalizing q₁ q₂ with
  | zero => exact ⟨by simpa using hf, funext Fin.rec0⟩
  | succ n ih =>
    cases r₁ using Fin.snocCases with | snoc rs₁ r₁
    cases r₂ using Fin.snocCases with | snoc rs₂ r₂
    simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc,
      Fin.val_castSucc, Fin.snoc_last, Fin.val_last] at hf
    rw [← add_rotate' (r₁ * g ^ n), ← add_rotate' (r₂ * g ^ n), pow_succ', ← mul_assoc, ← mul_assoc,
      ← add_assoc, ← add_assoc, ← add_mul, ← add_mul, ← mul_comm g, ← mul_comm g] at hf
    obtain ⟨hqr, hrs⟩ := ih
      (fun i => by simpa using hr₁ i.castSucc)
      (fun i => by simpa using hr₂ i.castSucc) hf
    obtain ⟨hq₁, hrr₁⟩ := div_modByMonic_unique q₁ r₁ hg ⟨rfl, by simpa using hr₁ (Fin.last n)⟩
    obtain ⟨hq₂, hrr₂⟩ := div_modByMonic_unique q₂ r₂ hg ⟨rfl, by simpa using hr₂ (Fin.last n)⟩
    exact ⟨hq₁.symm.trans (hqr ▸ hq₂), congrArg₂ Fin.snoc hrs (hrr₁.symm.trans (hqr ▸ hrr₂))⟩

