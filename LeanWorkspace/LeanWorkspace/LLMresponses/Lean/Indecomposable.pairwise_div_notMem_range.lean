FAIL
import Mathlib

variable {ι M G S : Type*} [Monoid M] [CommGroup G] [LinearOrder S]

theorem pairwise_div_notMem_range [InvolutiveInv ι]
    (v : ι → G)
    (hv_one : ∀ i, v i ≠ 1)
    (hv_inv : ∀ i, v i⁻¹ = (v i)⁻¹)
    (s t : Set ι)
    (hst : s ⊆ {i | IsMulIndecomposable v t i})
    (hv_t : ∀ i, i ∈ t ∨ i⁻¹ ∈ t) :
    s.Pairwise fun i j ↦ v i / v j ∉ Set.range v := by
  intro i hi j hj hij hmem
  rcases hmem with ⟨k, hk⟩
  have hi' : IsMulIndecomposable v t i := hst hi
  rcases hi' with ⟨hit, hindecomp⟩
  have hk_or_hkinv : k ∈ t ∨ k⁻¹ ∈ t := hv_t k
  cases hk_or_hkinv with
  | inl hkt =>
      have hjt : j ∈ t := by
        rcases hv_t j with hjt | hjinvt
        · exact hjt
        · have hkj1 : v k = 1 ∨ v i = 1 := hindecomp hkt hjinvt (by
            rw [hk]
            calc
              v i / v j = (v k) * (v j⁻¹) := by
                rw [hk]
              _ = v k * v (j⁻¹) := by rw [hv_inv]
            )
          have hji1 : v j = 1 := by
            cases hkj1 with
            | inl hk1 =>
                exfalso
                exact hv_one k hk1
            | inr hi1 =>
                exfalso
                exact hv_one i hi1
          exact False.elim (hv_one j hji1)
      have hdecomp : v i = v k * v j := by
        calc
          v i = (v i / v j) * v j := by
            simp [div_eq_mul_inv, mul_assoc]
          _ = v k * v j := by rw [← hk]
      have hk1_or_hj1 : v k = 1 ∨ v j = 1 := hindecomp hkt hjt hdecomp
      cases hk1_or_hj1 with
      | inl hk1 => exact hv_one k hk1
      | inr hj1 => exact hv_one j hj1
  | inr hkinvt =>
      have hk' : v (k⁻¹) = v i / v j := by
        rw [hv_inv]
        exact inv_eq_iff_eq_inv.mp (by rw [hk, inv_inv])
      have hkt' : k⁻¹ ∈ t := hkinvt
      have hjt : j ∈ t := by
        rcases hv_t j with hjt | hjinvt
        · exact hjt
        · have hkji1 : v (k⁻¹) = 1 ∨ v i = 1 := hindecomp hkt' hjinvt (by
            calc
              v i = (v i / v j) * v (j⁻¹) := by
                rw [div_eq_mul_inv, hv_inv]
                simp [mul_assoc]
              _ = v (k⁻¹) * v (j⁻¹) := by rw [hk']
          )
          have hj1 : v j = 1 := by
            cases hkji1 with
            | inl hk1 =>
                exfalso
                exact hv_one (k⁻¹) hk1
            | inr hi1 =>
                exfalso
                exact hv_one i hi1
          exact False.elim (hv_one j hj1)
      have hdecomp : v i = v (k⁻¹) * v j := by
        calc
          v i = (v i / v j) * v j := by
            simp [div_eq_mul_inv, mul_assoc]
          _ = v (k⁻¹) * v j := by rw [hk',]
      have hk1_or_hj1 : v (k⁻¹) = 1 ∨ v j = 1 := hindecomp hkt' hjt hdecomp
      cases hk1_or_hj1 with
      | inl hk1 => exact hv_one (k⁻¹) hk1
      | inr hj1 => exact hv_one j hj1
