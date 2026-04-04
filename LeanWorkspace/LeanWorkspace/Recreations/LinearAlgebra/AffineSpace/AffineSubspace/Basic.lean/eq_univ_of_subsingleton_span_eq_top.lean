import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P]

variable (k V) {p₁ p₂ : P}

variable (P)

variable {k V P}

theorem eq_univ_of_subsingleton_span_eq_top {s : Set P} (h₁ : s.Subsingleton)
    (h₂ : affineSpan k s = ⊤) : s = (Set.univ : Set P) := by
  obtain ⟨p, hp⟩ := AffineSubspace.nonempty_of_affineSpan_eq_top k V P h₂
  have : s = {p} := Subset.antisymm (fun q hq => h₁ hq hp) (by simp [hp])
  rw [this, eq_comm, ← subsingleton_iff_singleton (mem_univ p), subsingleton_univ_iff]
  exact AffineSubspace.subsingleton_of_subsingleton_span_eq_top h₁ h₂

