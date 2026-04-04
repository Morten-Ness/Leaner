import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P]

variable (k V) {p₁ p₂ : P}

variable (P)

variable {k V P}

theorem subsingleton_of_subsingleton_span_eq_top {s : Set P} (h₁ : s.Subsingleton)
    (h₂ : affineSpan k s = ⊤) : Subsingleton P := by
  obtain ⟨p, hp⟩ := AffineSubspace.nonempty_of_affineSpan_eq_top k V P h₂
  have : s = {p} := Subset.antisymm (fun q hq => h₁ hq hp) (by simp [hp])
  rw [this, AffineSubspace.ext_iff, AffineSubspace.coe_affineSpan_singleton,
    AffineSubspace.top_coe, eq_comm, ← subsingleton_iff_singleton (mem_univ _)] at h₂
  exact subsingleton_of_univ_subsingleton h₂

