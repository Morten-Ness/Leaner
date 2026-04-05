FAIL
import Mathlib

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [Ring k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2] [AddTorsor V2 P2]

variable [AddCommGroup V3] [AddTorsor V3 P3] [Module k V1] [Module k V2] [Module k V3]

variable {ι : Type*} {φv φp : ι → Type*} [(i : ι) → AddCommGroup (φv i)]
  [(i : ι) → Module k (φv i)] [(i : ι) → AddTorsor (φv i) (φp i)]

variable (fp : (i : ι) → (P1 →ᵃ[k] φp i)) (fv : (i : ι) → (P1 →ᵃ[k] φv i))
  (f' : ι → P1 →ᵃ[k] P2)

variable [Finite ι] [DecidableEq ι] {f g : ((i : ι) → φv i) →ᵃ[k] P2}

theorem pi_ext_zero (h : ∀ i x, f (Pi.single i x) = g (Pi.single i x)) (h₂ : f 0 = g 0) :
    f = g := by
  have hlin :
      f.toLinearMap = g.toLinearMap := by
    haveI : Fintype ι := Fintype.ofFinite ι
    ext x
    rw [show x = ∑ i, Pi.single i (x i) by
      ext i
      simp]
    simp only [LinearMap.map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hi0 := h i (0 : φv i)
    rw [AffineMap.linear_eq_zero_iff_eq_zero] at hi0
    simpa using hi0
  ext x
  rw [AffineMap.ext_iff]
  constructor
  · exact h₂
  · exact hlin
