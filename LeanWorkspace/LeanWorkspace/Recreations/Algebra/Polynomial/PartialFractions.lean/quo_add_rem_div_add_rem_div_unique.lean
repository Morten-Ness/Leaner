import Mathlib

open scoped algebraMap

variable {R : Type*} [CommRing R]

variable (K : Type*) [Field K] [Algebra R[X] K] [FaithfulSMul R[X] K]

theorem quo_add_rem_div_add_rem_div_unique {g₁ g₂ : R[X]} (hg₁ : g₁.Monic)
    (hg₂ : g₂.Monic) (hcoprime : IsCoprime g₁ g₂)
    {q₁ q₂ r₁₁ r₁₂ r₂₁ r₂₂ : R[X]}
    (hr₁₁ : r₁₁.degree < g₁.degree) (hr₁₂ : r₁₂.degree < g₁.degree)
    (hr₂₁ : r₂₁.degree < g₂.degree) (hr₂₂ : r₂₂.degree < g₂.degree)
    (hf : (↑q₁ + ↑r₁₁ / ↑g₁ + ↑r₂₁ / ↑g₂ : K) = ↑q₂ + ↑r₁₂ / ↑g₁ + ↑r₂₂ / ↑g₂) :
    q₁ = q₂ ∧ r₁₁ = r₁₂ ∧ r₂₁ = r₂₂ := by
  let g : Bool → R[X] := Bool.rec g₂ g₁
  let r₁ : Bool → R[X] := Bool.rec r₂₁ r₁₁
  let r₂ : Bool → R[X] := Bool.rec r₂₂ r₁₂
  have hg (i : Bool) (_ : i ∈ Finset.univ) : (g i).Monic := Bool.rec hg₂ hg₁ i
  have hcoprime : Set.Pairwise (Finset.univ : Finset Bool) fun i j => IsCoprime (g i) (g j) := by
    simp [g, Set.pairwise_insert, hcoprime, hcoprime.symm]
  have hr₁ (i : Bool) (_ : i ∈ Finset.univ) : (r₁ i).degree < (g i).degree := Bool.rec hr₂₁ hr₁₁ i
  have hr₂ (i : Bool) (_ : i ∈ Finset.univ) : (r₂ i).degree < (g i).degree := Bool.rec hr₂₂ hr₁₂ i
  refine (Polynomial.quo_add_sum_rem_div_unique K hg hcoprime hr₁ hr₂ ?_).imp_right fun h =>
    ⟨h true (Finset.mem_univ true), h false (Finset.mem_univ false)⟩
  simpa [g, r₁, r₂, add_assoc] using hf

