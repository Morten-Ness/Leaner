FAIL
import Mathlib

variable {R : Type*} [DivisionRing R] [CharZero R] {p : R}

theorem zmultiples_nsmul_eq_nsmul_iff {ψ θ : R ⧸ AddSubgroup.zmultiples p} {n : ℕ} (hz : n ≠ 0) :
    n • ψ = n • θ ↔ ∃ k : Fin n, ψ = θ + (k : ℕ) • (p / n : R) := by
  classical
  by_cases hp : p = 0
  · subst hp
    constructor
    · intro h
      refine ⟨⟨0, hz.bot_lt⟩, ?_⟩
      simp
    · rintro ⟨k, hk⟩
      simp [hk]
  · constructor
    · intro h
      have h' : n • (ψ - θ) = 0 := by
        simpa [nsmul_sub] using sub_eq_zero.mp h
      have htors :
          ∃ t : R ⧸ AddSubgroup.zmultiples p, n • t = 0 ∧ ψ = θ + t := by
        refine ⟨ψ - θ, ?_, by abel⟩
        simpa [h']
      rcases htors with ⟨t, ht, rfl⟩
      let k : Fin n := ⟨0, Nat.pos_of_ne_zero hz⟩
      refine ⟨k, ?_⟩
      have : t = 0 := by
        have hn : (n : R) ≠ 0 := by exact_mod_cast hz
        refine Quotient.inductionOn t ?_ t
        intro x
        change QuotientAddGroup.mk (n • x : R) = 0 at ht
        have hx : n • x ∈ AddSubgroup.zmultiples p := by
          simpa [QuotientAddGroup.eq_zero_iff] using ht
        rcases hx with ⟨m, hm⟩
        have hm' : (n : R) * x = m * p := by
          simpa [zsmul_eq_mul, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hm
        have : x = (m / n) * p := by
          apply (mul_right_inj' hn).mp
          rw [mul_assoc, div_mul_cancel₀ _ hn, hm', mul_assoc]
        apply Quotient.sound
        rw [this]
        refine ⟨m / n, ?_⟩
        ring
      simp [this]
    · rintro ⟨k, hk⟩
      subst hk
      rw [nsmul_add]
      congr 1
      change n • (((k : ℕ) • ((p / n : R) : R ⧸ AddSubgroup.zmultiples p))) = 0
      rw [← nsmul_eq_mul, ← nsmul_eq_mul, smul_smul]
      change ((n * (k : ℕ)) : ℕ) • ((p / n : R) : R ⧸ AddSubgroup.zmultiples p) = 0
      rw [QuotientAddGroup.eq_zero_iff]
      refine ⟨k, ?_⟩
      change (((n * (k : ℕ)) : ℤ) • (p / n : R)) = (k : ℤ) • p
      rw [zsmul_eq_mul, zsmul_eq_mul]
      norm_num [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
