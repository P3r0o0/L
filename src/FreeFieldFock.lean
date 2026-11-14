import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import FreeFieldWick
import WightmanBridge

open scoped ComplexConjugate Topology BigOperators Matrix InnerProductSpace
open Geometry Geometry.MatrixAnalysis MeasureTheory Filter Complex Matrix

namespace QFT

noncomputable section

structure MassShellModeData {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (m : ℝ) (η : ℂ) (C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ) where
  ν : ℕ
  hη : η = 1 ∨ η = -1
  w : Fin ν → (Fin 3 → ℝ) → ι → ℂ
  measurable_w : ∀ (s : Fin ν) (α : ι), Measurable (fun p : Fin 3 → ℝ => w s p α)
  M : ℝ
  hM : 0 ≤ M
  norm_w_le : ∀ (s : Fin ν) (p : Fin 3 → ℝ) (α : ι), ‖w s p α‖ ≤ M
  factor_weight : ∀ (p : Fin 3 → ℝ) (α β : ι),
    ∑ γ : ι, S.C α γ * massShellWeight m C ![γ, β] p =
      ∑ s : Fin ν, star (w s p α) * w s p β

noncomputable def kgModeData {m : ℝ} (hm : 0 < m) :
    MassShellModeData trivialRep trivialStarStructure m 1 massiveKGCoeff where
  ν := 1
  hη := Or.inl rfl
  w _ p _ := (((Real.sqrt (2 * massShellEnergy m p))⁻¹ : ℝ) : ℂ)
  measurable_w _ _ :=
    Complex.continuous_ofReal.measurable.comp
      (((continuous_const.mul (continuous_massShellEnergy m)).sqrt).inv₀
        (fun p => by
          change Real.sqrt (2 * massShellEnergy m p) ≠ 0
          exact Real.sqrt_ne_zero'.mpr (by linarith [massShellEnergy_pos hm p]))).measurable
  M := (Real.sqrt (2 * m))⁻¹
  hM := inv_nonneg.mpr (Real.sqrt_nonneg _)
  norm_w_le _ p _ := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    exact inv_anti₀ (Real.sqrt_pos.mpr (by linarith))
      (Real.sqrt_le_sqrt (by linarith [massShellEnergy_ge_mass hm p]))
  factor_weight p α β := by
    cases α
    cases β
    simp only [Fin.sum_univ_one, Fintype.univ_punit, Finset.sum_singleton,
      trivialStarStructure, Matrix.one_apply_eq, one_mul,
      massShellWeight, massiveKGCoeff, mul_one]
    have hpos : 0 ≤ 2 * massShellEnergy m p := by linarith [massShellEnergy_pos hm p]
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      ← mul_inv, Real.mul_self_sqrt hpos]
    push_cast
    rfl

def diracModeRaw (m : ℝ) : Fin 2 → (Fin 3 → ℝ) → (Fin 2 ⊕ Fin 2) → ℂ
  | 0, _, Sum.inl 0 => 0
  | 0, _, Sum.inl 1 => (m : ℂ) * Complex.I
  | 0, p, Sum.inr 0 => ((massShellEnergy m p : ℂ) + (p 2 : ℂ))
  | 0, p, Sum.inr 1 => ((p 0 : ℂ) - (p 1 : ℂ) * Complex.I)
  | 1, p, Sum.inl 0 => -Complex.I * ((massShellEnergy m p : ℂ) + (p 2 : ℂ))
  | 1, p, Sum.inl 1 => -Complex.I * ((p 0 : ℂ) + (p 1 : ℂ) * Complex.I)
  | 1, _, Sum.inr 0 => 0
  | 1, _, Sum.inr 1 => (m : ℂ)

lemma continuous_diracModeRaw (m : ℝ) (s : Fin 2) (α : Fin 2 ⊕ Fin 2) :
    Continuous (fun p : Fin 3 → ℝ => diracModeRaw m s p α) := by
  fin_cases s <;>
    rcases α with i | i <;>
    fin_cases i
  · exact continuous_const
  · exact continuous_const
  · exact (Complex.continuous_ofReal.comp (continuous_massShellEnergy m)).add
      (Complex.continuous_ofReal.comp (continuous_apply 2))
  · exact (Complex.continuous_ofReal.comp (continuous_apply 0)).sub
      ((Complex.continuous_ofReal.comp (continuous_apply 1)).mul continuous_const)
  · exact continuous_const.mul
      ((Complex.continuous_ofReal.comp (continuous_massShellEnergy m)).add
        (Complex.continuous_ofReal.comp (continuous_apply 2)))
  · exact continuous_const.mul
      ((Complex.continuous_ofReal.comp (continuous_apply 0)).add
        ((Complex.continuous_ofReal.comp (continuous_apply 1)).mul continuous_const))
  · exact continuous_const
  · exact continuous_const

noncomputable def diracModeScale (m : ℝ) (p : Fin 3 → ℝ) : ℝ :=
  (Real.sqrt (2 * massShellEnergy m p * (massShellEnergy m p + p 2)))⁻¹

lemma diracModeDenom_pos {m : ℝ} (hm : 0 < m) (p : Fin 3 → ℝ) :
    0 < 2 * massShellEnergy m p * (massShellEnergy m p + p 2) :=
  mul_pos (mul_pos zero_lt_two (massShellEnergy_pos hm p))
    (massShellEnergy_add_third_pos hm p)

lemma continuous_diracModeScale {m : ℝ} (hm : 0 < m) :
    Continuous (diracModeScale m) := by
  unfold diracModeScale
  refine Continuous.inv₀ ?_ (fun p => Real.sqrt_ne_zero'.mpr (diracModeDenom_pos hm p))
  exact ((continuous_const.mul (continuous_massShellEnergy m)).mul
    ((continuous_massShellEnergy m).add (continuous_apply 2))).sqrt

lemma normSq_diracModeRaw_le {m : ℝ} (hm : 0 < m) (s : Fin 2)
    (p : Fin 3 → ℝ) (α : Fin 2 ⊕ Fin 2) :
    Complex.normSq (diracModeRaw m s p α) ≤
      2 * massShellEnergy m p * (massShellEnergy m p + p 2) := by
  have he_pos : 0 < massShellEnergy m p := massShellEnergy_pos hm p
  have hp_add_pos : 0 < massShellEnergy m p + p 2 := massShellEnergy_add_third_pos hm p
  have h_msq : m ^ 2 + (p 0) ^ 2 + (p 1) ^ 2 =
      (massShellEnergy m p - p 2) * (massShellEnergy m p + p 2) := by
    have hsq := massShellEnergy_sq m p
    unfold massShellSpatialSq at hsq
    linarith
  have hp2_bounds : -massShellEnergy m p ≤ p 2 ∧ p 2 ≤ massShellEnergy m p := by
    have hsq : (p 2) ^ 2 ≤ (massShellEnergy m p) ^ 2 := by
      have h1 := massShellEnergy_sq m p
      unfold massShellSpatialSq at h1
      nlinarith [sq_nonneg m, sq_nonneg (p 0), sq_nonneg (p 1)]
    exact abs_le_of_sq_le_sq' hsq he_pos.le
  have h_sub_le : massShellEnergy m p - p 2 ≤ 2 * massShellEnergy m p := by
    linarith [hp2_bounds.1]
  have h_add_le : massShellEnergy m p + p 2 ≤ 2 * massShellEnergy m p := by
    linarith [hp2_bounds.2]
  have h_prod1 : (massShellEnergy m p - p 2) * (massShellEnergy m p + p 2) ≤
      2 * massShellEnergy m p * (massShellEnergy m p + p 2) :=
    mul_le_mul_of_nonneg_right h_sub_le hp_add_pos.le
  have h_prod2 : (massShellEnergy m p + p 2) ^ 2 ≤
      2 * massShellEnergy m p * (massShellEnergy m p + p 2) := by
    rw [sq]
    exact mul_le_mul_of_nonneg_right h_add_le hp_add_pos.le
  fin_cases s <;>
    rcases α with i | i <;>
    fin_cases i
  · simp only [diracModeRaw, map_zero, ge_iff_le]
    exact (diracModeDenom_pos hm p).le
  · simp only [diracModeRaw, map_mul, Complex.normSq_ofReal, Complex.normSq_I, mul_one]
    nlinarith [sq_nonneg (p 0), sq_nonneg (p 1), h_msq, h_prod1]
  · have h_eq : ((massShellEnergy m p : ℂ) + (p 2 : ℂ)) =
        ((massShellEnergy m p + p 2 : ℝ) : ℂ) := by push_cast; rfl
    change Complex.normSq ((massShellEnergy m p : ℂ) + (p 2 : ℂ)) ≤ _
    rw [h_eq, Complex.normSq_ofReal]
    nlinarith [h_prod2]
  · have h_re_im : Complex.normSq ((p 0 : ℂ) - (p 1 : ℂ) * Complex.I) =
        (p 0) ^ 2 + (p 1) ^ 2 := by
      have hz : (p 0 : ℂ) - (p 1 : ℂ) * Complex.I = ⟨p 0, -(p 1)⟩ := by
        apply Complex.ext <;> simp
      rw [hz, Complex.normSq_mk]
      ring
    change Complex.normSq ((p 0 : ℂ) - (p 1 : ℂ) * Complex.I) ≤ _
    rw [h_re_im]
    nlinarith [sq_nonneg m, h_msq, h_prod1]
  · have h_eq : ((massShellEnergy m p : ℂ) + (p 2 : ℂ)) =
        ((massShellEnergy m p + p 2 : ℝ) : ℂ) := by push_cast; rfl
    change Complex.normSq (-Complex.I * ((massShellEnergy m p : ℂ) + (p 2 : ℂ))) ≤ _
    rw [map_mul, Complex.normSq_neg, Complex.normSq_I, one_mul, h_eq, Complex.normSq_ofReal]
    nlinarith [h_prod2]
  · have h_re_im : Complex.normSq ((p 0 : ℂ) + (p 1 : ℂ) * Complex.I) =
        (p 0) ^ 2 + (p 1) ^ 2 := by
      have hz : (p 0 : ℂ) + (p 1 : ℂ) * Complex.I = ⟨p 0, p 1⟩ := by
        apply Complex.ext <;> simp
      rw [hz, Complex.normSq_mk]
      ring
    change Complex.normSq (-Complex.I * ((p 0 : ℂ) + (p 1 : ℂ) * Complex.I)) ≤ _
    rw [map_mul, Complex.normSq_neg, Complex.normSq_I, one_mul, h_re_im]
    nlinarith [sq_nonneg m, h_msq, h_prod1]
  · simp only [diracModeRaw, map_zero, ge_iff_le]
    exact (diracModeDenom_pos hm p).le
  · simp only [diracModeRaw, Complex.normSq_ofReal]
    nlinarith [sq_nonneg (p 0), sq_nonneg (p 1), h_msq, h_prod1]

lemma diracModeRaw_sos (m : ℝ) (p : Fin 3 → ℝ) (α β : Fin 2 ⊕ Fin 2) :
    ((massShellEnergy m p + p 2 : ℝ) : ℂ) *
      diracMassShellCoeff m ![Sum.swap α, β] (massShellVec m p) =
    ∑ s : Fin 2, star (diracModeRaw m s p α) * diracModeRaw m s p β := by
  let q := massShellVec m p
  have h_msq : (m : ℂ) ^ 2 =
      (q 0 : ℂ) ^ 2 - (q 1 : ℂ) ^ 2 - (q 2 : ℂ) ^ 2 - (q 3 : ℂ) ^ 2 := by
    have hr : m ^ 2 = (q 0) ^ 2 - (q 1) ^ 2 - (q 2) ^ 2 - (q 3) ^ 2 := by
      dsimp [q, massShellVec]
      rw [massShellEnergy_sq]
      unfold massShellSpatialSq
      ring
    exact_mod_cast hr
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [pow_succ, Complex.I_sq]
    ring
  have hI4 : Complex.I ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, Complex.I_sq]
    ring
  have h_bilin : ∀ (ξ ζ : Fin 2 ⊕ Fin 2 → ℂ),
      ((q 0 : ℂ) + (q 3 : ℂ)) *
        (∑ γ : Fin 2 ⊕ Fin 2, ∑ γ' : Fin 2 ⊕ Fin 2,
          (starRingEnd ℂ) (ξ γ) * diracMassShellCoeff m ![Sum.swap γ, γ'] q * ζ γ') =
      ∑ γ : Fin 2 ⊕ Fin 2, ∑ γ' : Fin 2 ⊕ Fin 2,
        (starRingEnd ℂ) (ξ γ) *
          (∑ s : Fin 2, (starRingEnd ℂ) (diracModeRaw m s p γ) * diracModeRaw m s p γ') *
          ζ γ' := by
    intro ξ ζ
    have hL :
        (∑ γ : Fin 2 ⊕ Fin 2, ∑ γ' : Fin 2 ⊕ Fin 2,
          (starRingEnd ℂ) (ξ γ) * diracMassShellCoeff m ![Sum.swap γ, γ'] q * ζ γ') =
        (starRingEnd ℂ) (ξ (Sum.inl 0)) *
          (((q 0 : ℂ) + (q 3 : ℂ)) * ζ (Sum.inl 0) +
            ((q 1 : ℂ) + (q 2 : ℂ) * Complex.I) * ζ (Sum.inl 1)) +
        (starRingEnd ℂ) (ξ (Sum.inl 1)) *
          (((q 1 : ℂ) - (q 2 : ℂ) * Complex.I) * ζ (Sum.inl 0) +
            ((q 0 : ℂ) - (q 3 : ℂ)) * ζ (Sum.inl 1)) +
        (starRingEnd ℂ) (ξ (Sum.inr 0)) *
          (((q 0 : ℂ) + (q 3 : ℂ)) * ζ (Sum.inr 0) +
            ((q 1 : ℂ) - (q 2 : ℂ) * Complex.I) * ζ (Sum.inr 1)) +
        (starRingEnd ℂ) (ξ (Sum.inr 1)) *
          (((q 1 : ℂ) + (q 2 : ℂ) * Complex.I) * ζ (Sum.inr 0) +
            ((q 0 : ℂ) - (q 3 : ℂ)) * ζ (Sum.inr 1)) +
        (m : ℂ) * Complex.I *
          ((starRingEnd ℂ) (ξ (Sum.inl 0)) * ζ (Sum.inr 1) -
            (starRingEnd ℂ) (ξ (Sum.inl 1)) * ζ (Sum.inr 0) +
            (starRingEnd ℂ) (ξ (Sum.inr 0)) * ζ (Sum.inl 1) -
            (starRingEnd ℂ) (ξ (Sum.inr 1)) * ζ (Sum.inl 0)) := by
      simp only [Fintype.sum_sum_type, Fin.sum_univ_two, Fin.isValue, Sum.swap_inl,
        Sum.swap_inr, diracMassShellCoeff, diracEpsilon_inl_inl, diracEpsilon_inr_inr,
        diracEpsilon_inl_inr, diracEpsilon_inr_inl, diracSlashCoeff_inl_inl,
        diracSlashCoeff_inr_inr, diracSlashCoeff_inl_inr, diracSlashCoeff_inr_inl,
        weylEpsilon_zero_zero, weylEpsilon_zero_one, weylEpsilon_one_zero,
        weylEpsilon_one_one, vec_to_spinor_apply_00, vec_to_spinor_apply_01,
        vec_to_spinor_apply_10, vec_to_spinor_apply_11]
      ring
    have hq0 : massShellEnergy m p = q 0 := rfl
    have hp0 : p 0 = q 1 := rfl
    have hp1 : p 1 = q 2 := rfl
    have hp2 : p 2 = q 3 := rfl
    rw [hL]
    simp only [Fintype.sum_sum_type, Fin.sum_univ_two, Fin.isValue, diracModeRaw,
      hq0, hp0, hp1, hp2, map_mul, map_add, map_sub, map_neg, map_zero,
      Complex.conj_ofReal, Complex.conj_I]
    ring_nf
    simp only [Complex.I_sq, hI3, hI4, h_msq]
    ring
  have h_eval := h_bilin (fun γ => if γ = α then 1 else 0) (fun γ' => if γ' = β then 1 else 0)
  simp only [apply_ite (starRingEnd ℂ), map_one, map_zero, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h_eval
  have hq03 : ((massShellEnergy m p + p 2 : ℝ) : ℂ) = (q 0 : ℂ) + (q 3 : ℂ) := by
    dsimp [q, massShellVec]
    push_cast
    rfl
  rw [hq03]
  simpa only [Complex.star_def] using h_eval

noncomputable def diracModeData {m : ℝ} (hm : 0 < m) :
    MassShellModeData diracRep diracStarStructure m (-1) (diracMassShellCoeff m) where
  ν := 2
  hη := Or.inr rfl
  w s p α := (diracModeScale m p : ℂ) * diracModeRaw m s p α
  measurable_w s α :=
    (Complex.continuous_ofReal.comp (continuous_diracModeScale hm)).measurable.mul
      (continuous_diracModeRaw m s α).measurable
  M := 1
  hM := zero_le_one
  norm_w_le s p α := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hden : 0 < 2 * massShellEnergy m p * (massShellEnergy m p + p 2) :=
      diracModeDenom_pos hm p
    have hsc_nn : 0 ≤ diracModeScale m p := inv_nonneg.mpr (Real.sqrt_nonneg _)
    rw [abs_of_nonneg hsc_nn, Complex.norm_def]
    have hle := Real.sqrt_le_sqrt (normSq_diracModeRaw_le hm s p α)
    calc diracModeScale m p * Real.sqrt (Complex.normSq (diracModeRaw m s p α))
        ≤ diracModeScale m p *
            Real.sqrt (2 * massShellEnergy m p * (massShellEnergy m p + p 2)) :=
          mul_le_mul_of_nonneg_left hle hsc_nn
      _ = 1 := inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr hden)
  factor_weight p α β := by
    have hC_sum : ∑ γ : Fin 2 ⊕ Fin 2,
        diracStarStructure.C α γ * massShellWeight m (diracMassShellCoeff m) ![γ, β] p =
        massShellWeight m (diracMassShellCoeff m) ![Sum.swap α, β] p := by
      have h_entry : ∀ γ : Fin 2 ⊕ Fin 2, diracStarStructure.C α γ =
          if γ = Sum.swap α then 1 else 0 := by
        intro γ
        rcases α with i | i <;> rcases γ with j | j <;> fin_cases i <;> fin_cases j <;>
          simp [diracStarStructure, chiralDoubleStarStructure, Matrix.fromBlocks]
      simp_rw [h_entry, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    rw [hC_sum]
    have hden_pos : 0 < 2 * massShellEnergy m p * (massShellEnergy m p + p 2) :=
      diracModeDenom_pos hm p
    have hsc_sq : (diracModeScale m p : ℂ) * (diracModeScale m p : ℂ) =
        (((2 * massShellEnergy m p * (massShellEnergy m p + p 2))⁻¹ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      dsimp [diracModeScale]
      rw [← mul_inv, Real.mul_self_sqrt hden_pos.le]
    have hrhs :
        (∑ s : Fin 2,
          star ((diracModeScale m p : ℂ) * diracModeRaw m s p α) *
            ((diracModeScale m p : ℂ) * diracModeRaw m s p β)) =
        (((2 * massShellEnergy m p * (massShellEnergy m p + p 2))⁻¹ : ℝ) : ℂ) *
          ∑ s : Fin 2, star (diracModeRaw m s p α) * diracModeRaw m s p β := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [star_mul']
      have hstar_sc : star (diracModeScale m p : ℂ) = (diracModeScale m p : ℂ) := by
        rw [Complex.star_def, Complex.conj_ofReal]
      rw [hstar_sc]
      calc (diracModeScale m p : ℂ) * star (diracModeRaw m s p α) *
            ((diracModeScale m p : ℂ) * diracModeRaw m s p β)
          = ((diracModeScale m p : ℂ) * (diracModeScale m p : ℂ)) *
              (star (diracModeRaw m s p α) * diracModeRaw m s p β) := by ring
        _ = (((2 * massShellEnergy m p * (massShellEnergy m p + p 2))⁻¹ : ℝ) : ℂ) *
              (star (diracModeRaw m s p α) * diracModeRaw m s p β) := by rw [hsc_sq]
    rw [hrhs, ← diracModeRaw_sos m p α β]
    unfold massShellWeight
    have he_ne : ((massShellEnergy m p : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (massShellEnergy_pos hm p).ne'
    have hp_ne : ((massShellEnergy m p : ℝ) : ℂ) + (p 2 : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_add]
      exact Complex.ofReal_ne_zero.mpr (massShellEnergy_add_third_pos hm p).ne'
    push_cast
    field_simp [he_ne, hp_ne]

abbrev FockSectorDom (ν r : ℕ) : Type :=
  (Fin r → Fin 3 → ℝ) × (Fin r → Fin ν)

noncomputable def fockSectorMeasure (ν r : ℕ) : Measure (FockSectorDom ν r) :=
  volume.prod Measure.count

instance instSigmaFiniteFockSectorMeasure (ν r : ℕ) :
    SigmaFinite (fockSectorMeasure ν r) := by
  unfold fockSectorMeasure
  infer_instance

abbrev FockOmega (ν : ℕ) : Type :=
  Σ r : ℕ, FockSectorDom ν r

lemma measurable_fockSigmaMk (ν r : ℕ) :
    Measurable (Sigma.mk r : FockSectorDom ν r → FockOmega ν) := by
  intro U hU
  exact (MeasurableSpace.measurableSet_iInf.mp hU) r

lemma measurableSet_fockOmega_iff (ν : ℕ) (S : Set (FockOmega ν)) :
    MeasurableSet S ↔ ∀ r : ℕ, MeasurableSet (Sigma.mk r ⁻¹' S) :=
  MeasurableSpace.measurableSet_iInf

noncomputable def fockMeasure (ν : ℕ) : Measure (FockOmega ν) :=
  Measure.sum (fun r : ℕ => (fockSectorMeasure ν r).map (Sigma.mk r))

abbrev FockHilbert (ν : ℕ) : Type :=
  MeasureTheory.Lp ℂ 2 (fockMeasure ν)

def sectorToOmega (ν r : ℕ) (g : FockSectorDom ν r → ℂ) : FockOmega ν → ℂ :=
  fun a => if h : a.1 = r then g (h ▸ a.2) else 0

@[simp]
lemma sectorToOmega_sigmaMk_eq (ν r : ℕ) (g : FockSectorDom ν r → ℂ)
    (x : FockSectorDom ν r) :
    sectorToOmega ν r g ⟨r, x⟩ = g x := by
  simp [sectorToOmega]

lemma sectorToOmega_sigmaMk_ne (ν : ℕ) {r r' : ℕ} (hne : r' ≠ r)
    (g : FockSectorDom ν r → ℂ) (x : FockSectorDom ν r') :
    sectorToOmega ν r g ⟨r', x⟩ = 0 := by
  simp [sectorToOmega, hne]

lemma sectorToOmega_mul_ne (ν : ℕ) {r₁ r₂ : ℕ} (hne : r₁ ≠ r₂)
    (g₁ : FockSectorDom ν r₁ → ℂ) (g₂ : FockSectorDom ν r₂ → ℂ) (a : FockOmega ν) :
    star (sectorToOmega ν r₁ g₁ a) * sectorToOmega ν r₂ g₂ a = 0 := by
  rcases a with ⟨r', x⟩
  by_cases h1 : r' = r₁
  · subst h1
    rw [sectorToOmega_sigmaMk_ne ν hne g₂ x, mul_zero]
  · rw [sectorToOmega_sigmaMk_ne ν h1 g₁ x, star_zero, zero_mul]

lemma measurable_sectorToOmega {ν r : ℕ} {g : FockSectorDom ν r → ℂ} (hg : Measurable g) :
    Measurable (sectorToOmega ν r g) := by
  intro U hU
  rw [measurableSet_fockOmega_iff]
  intro r'
  by_cases h : r' = r
  · subst h
    have hpre : Sigma.mk r' ⁻¹' (sectorToOmega ν r' g ⁻¹' U) = g ⁻¹' U := by
      ext x
      simp [sectorToOmega]
    rw [hpre]
    exact hg hU
  · by_cases h0 : (0 : ℂ) ∈ U
    · have hpre : Sigma.mk r' ⁻¹' (sectorToOmega ν r g ⁻¹' U) = Set.univ := by
        ext x
        simp [sectorToOmega, h, h0]
      rw [hpre]
      exact MeasurableSet.univ
    · have hpre : Sigma.mk r' ⁻¹' (sectorToOmega ν r g ⁻¹' U) = ∅ := by
        ext x
        simp [sectorToOmega, h, h0]
      rw [hpre]
      exact MeasurableSet.empty

lemma memLp_sectorToOmega {ν r : ℕ} {g : FockSectorDom ν r → ℂ} (hg_meas : Measurable g)
    (hg : MemLp g 2 (fockSectorMeasure ν r)) :
    MemLp (sectorToOmega ν r g) 2 (fockMeasure ν) := by
  refine ⟨(measurable_sectorToOmega hg_meas).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h2 : ENNReal.toReal 2 = 2 := by norm_num
  have h_sum :
      ∫⁻ a : FockOmega ν, (‖sectorToOmega ν r g a‖ₑ) ^ (2 : ℝ) ∂(fockMeasure ν) =
      ∫⁻ x : FockSectorDom ν r, (‖g x‖ₑ) ^ (2 : ℝ) ∂(fockSectorMeasure ν r) := by
    unfold fockMeasure
    have h_meas_nn : Measurable (fun a : FockOmega ν =>
        (‖sectorToOmega ν r g a‖ₑ) ^ (2 : ℝ)) :=
      ((measurable_sectorToOmega hg_meas).enorm).pow_const (2 : ℝ)
    rw [lintegral_sum_measure, tsum_eq_single r]
    · rw [lintegral_map h_meas_nn (measurable_fockSigmaMk ν r)]
      simp [sectorToOmega]
    · intro r' hne
      rw [lintegral_map h_meas_nn (measurable_fockSigmaMk ν r')]
      simp [sectorToOmega, hne]
  have hg_norm := hg.eLpNorm_lt_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at hg_norm
  rwa [h2, h_sum, ← h2]

noncomputable def liftSectorToFock (ν r : ℕ) (g : FockSectorDom ν r → ℂ)
    (hg_meas : Measurable g) (hg : MemLp g 2 (fockSectorMeasure ν r)) : FockHilbert ν :=
  (memLp_sectorToOmega hg_meas hg).toLp (sectorToOmega ν r g)

lemma integral_fockMeasure_mul_sectorToOmega_eq {ν r : ℕ}
    {g₁ g₂ : FockSectorDom ν r → ℂ}
    (hg₁_meas : Measurable g₁) (hg₁ : MemLp g₁ 2 (fockSectorMeasure ν r))
    (hg₂_meas : Measurable g₂) (hg₂ : MemLp g₂ 2 (fockSectorMeasure ν r)) :
    (∫ a : FockOmega ν,
      star (sectorToOmega ν r g₁ a) * sectorToOmega ν r g₂ a ∂(fockMeasure ν)) =
    ∫ x : FockSectorDom ν r, star (g₁ x) * g₂ x ∂(fockSectorMeasure ν r) := by
  let F : FockOmega ν → ℂ := fun a => star (sectorToOmega ν r g₁ a) * sectorToOmega ν r g₂ a
  have hF_meas : Measurable F :=
    (continuous_star.measurable.comp (measurable_sectorToOmega hg₁_meas)).mul
      (measurable_sectorToOmega hg₂_meas)
  have hF_int : Integrable F (fockMeasure ν) := by
    have h1 := memLp_sectorToOmega hg₁_meas hg₁
    have h2 := memLp_sectorToOmega hg₂_meas hg₂
    have h_inner := L2.integrable_inner (𝕜 := ℂ) (h1.toLp _) (h2.toLp _)
    refine h_inner.congr ?_
    filter_upwards [h1.coeFn_toLp, h2.coeFn_toLp] with a ha1 ha2
    simp [F, RCLike.inner_apply, ha1, ha2, mul_comm]
  change ∫ a : FockOmega ν, F a ∂(fockMeasure ν) = _
  unfold fockMeasure
  rw [integral_sum_measure hF_int, tsum_eq_single r]
  · rw [integral_map (measurable_fockSigmaMk ν r).aemeasurable hF_meas.aestronglyMeasurable]
    simp [F, sectorToOmega]
  · intro r' hne
    rw [integral_map (measurable_fockSigmaMk ν r').aemeasurable hF_meas.aestronglyMeasurable]
    simp [F, sectorToOmega, hne]

theorem inner_liftSectorToFock_eq {ν r : ℕ}
    {g₁ g₂ : FockSectorDom ν r → ℂ}
    (hg₁_meas : Measurable g₁) (hg₁ : MemLp g₁ 2 (fockSectorMeasure ν r))
    (hg₂_meas : Measurable g₂) (hg₂ : MemLp g₂ 2 (fockSectorMeasure ν r)) :
    ⟪liftSectorToFock ν r g₁ hg₁_meas hg₁, liftSectorToFock ν r g₂ hg₂_meas hg₂⟫_ℂ =
      ∫ x : FockSectorDom ν r, star (g₁ x) * g₂ x ∂(fockSectorMeasure ν r) := by
  rw [L2.inner_def]
  have h_congr :
      (∫ a : FockOmega ν,
        ⟪(liftSectorToFock ν r g₁ hg₁_meas hg₁ : FockOmega ν → ℂ) a,
          (liftSectorToFock ν r g₂ hg₂_meas hg₂ : FockOmega ν → ℂ) a⟫_ℂ ∂(fockMeasure ν)) =
      ∫ a : FockOmega ν,
        star (sectorToOmega ν r g₁ a) * sectorToOmega ν r g₂ a ∂(fockMeasure ν) := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_sectorToOmega hg₁_meas hg₁).coeFn_toLp,
      (memLp_sectorToOmega hg₂_meas hg₂).coeFn_toLp] with a ha1 ha2
    unfold liftSectorToFock
    rw [ha1, ha2]
    simp [RCLike.inner_apply, mul_comm]
  rw [h_congr, integral_fockMeasure_mul_sectorToOmega_eq hg₁_meas hg₁ hg₂_meas hg₂]

theorem inner_liftSectorToFock_ne {ν r₁ r₂ : ℕ} (hne : r₁ ≠ r₂)
    {g₁ : FockSectorDom ν r₁ → ℂ} {g₂ : FockSectorDom ν r₂ → ℂ}
    (hg₁_meas : Measurable g₁) (hg₁ : MemLp g₁ 2 (fockSectorMeasure ν r₁))
    (hg₂_meas : Measurable g₂) (hg₂ : MemLp g₂ 2 (fockSectorMeasure ν r₂)) :
    ⟪liftSectorToFock ν r₁ g₁ hg₁_meas hg₁, liftSectorToFock ν r₂ g₂ hg₂_meas hg₂⟫_ℂ = 0 := by
  rw [L2.inner_def]
  have h_zero :
      (fun a : FockOmega ν =>
        ⟪(liftSectorToFock ν r₁ g₁ hg₁_meas hg₁ : FockOmega ν → ℂ) a,
          (liftSectorToFock ν r₂ g₂ hg₂_meas hg₂ : FockOmega ν → ℂ) a⟫_ℂ) =ᶠ[ae (fockMeasure ν)]
      0 := by
    filter_upwards [(memLp_sectorToOmega hg₁_meas hg₁).coeFn_toLp,
      (memLp_sectorToOmega hg₂_meas hg₂).coeFn_toLp] with a ha1 ha2
    unfold liftSectorToFock
    rw [ha1, ha2]
    have hmul := sectorToOmega_mul_ne ν hne g₁ g₂ a
    simpa [RCLike.inner_apply, mul_comm] using hmul
  rw [integral_congr_ae h_zero]
  simp

def fockSectorPermEquiv (ν r : ℕ) (π : Equiv.Perm (Fin r)) :
    FockSectorDom ν r ≃ᵐ FockSectorDom ν r where
  toFun x := (x.1 ∘ π, x.2 ∘ π)
  invFun x := (x.1 ∘ π.symm, x.2 ∘ π.symm)
  left_inv x := by
    rcases x with ⟨k, s⟩
    apply Prod.ext <;> ext a <;> simp
  right_inv x := by
    rcases x with ⟨k, s⟩
    apply Prod.ext <;> ext a <;> simp
  measurable_toFun :=
    (measurable_pi_lambda _ (fun a => (measurable_pi_apply (π a)).comp measurable_fst)).prodMk
      (measurable_pi_lambda _ (fun a => (measurable_pi_apply (π a)).comp measurable_snd))
  measurable_invFun :=
    (measurable_pi_lambda _
      (fun a => (measurable_pi_apply (π.symm a)).comp measurable_fst)).prodMk
      (measurable_pi_lambda _ (fun a => (measurable_pi_apply (π.symm a)).comp measurable_snd))

@[simp]
lemma fockSectorPermEquiv_apply (ν r : ℕ) (π : Equiv.Perm (Fin r))
    (x : FockSectorDom ν r) :
    fockSectorPermEquiv ν r π x = (x.1 ∘ π, x.2 ∘ π) := rfl

lemma measurePreserving_fockSectorPermEquiv (ν r : ℕ) (π : Equiv.Perm (Fin r)) :
    MeasurePreserving (fockSectorPermEquiv ν r π)
      (fockSectorMeasure ν r) (fockSectorMeasure ν r) := by
  have h1 : MeasurePreserving (fun k : Fin r → Fin 3 → ℝ => k ∘ π) volume volume := by
    have heq : (fun k : Fin r → Fin 3 → ℝ => k ∘ π) =
        ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin r => Fin 3 → ℝ) π.symm) := by
      funext k a
      change k (π a) = Equiv.piCongrLeft (fun _ : Fin r => Fin 3 → ℝ) π.symm k a
      rw [Equiv.piCongrLeft_apply]
      simp
    rw [heq]
    exact volume_measurePreserving_piCongrLeft (fun _ : Fin r => Fin 3 → ℝ) π.symm
  have h2 : MeasurePreserving (fun s : Fin r → Fin ν => s ∘ π)
      Measure.count Measure.count := by
    let e : (Fin r → Fin ν) ≃ (Fin r → Fin ν) :=
      { toFun := fun s => s ∘ π
        invFun := fun s => s ∘ π.symm
        left_inv := fun s => by ext a; simp
        right_inv := fun s => by ext a; simp }
    have hm : Measurable e :=
      measurable_pi_lambda _ (fun a => measurable_pi_apply (π a))
    change MeasurePreserving e Measure.count Measure.count
    refine ⟨hm, ?_⟩
    ext S hS
    rw [Measure.map_apply hm hS, Measure.count_apply (hS.preimage hm), Measure.count_apply hS,
      ← e.injective.encard_image, e.image_preimage]
  exact MeasurePreserving.prod h1 h2

noncomputable def symmSector (ν r : ℕ) (η : ℂ) (F : FockSectorDom ν r → ℂ) :
    FockSectorDom ν r → ℂ :=
  fun x => (((r.factorial : ℝ).sqrt⁻¹ : ℝ) : ℂ) *
    ∑ π : Equiv.Perm (Fin r), η ^ permInversions π * F (fockSectorPermEquiv ν r π x)

lemma measurable_symmSector {ν r : ℕ} (η : ℂ) {F : FockSectorDom ν r → ℂ}
    (hF : Measurable F) :
    Measurable (symmSector ν r η F) :=
  measurable_const.mul <|
    Finset.measurable_sum Finset.univ (fun π _ =>
      measurable_const.mul (hF.comp (fockSectorPermEquiv ν r π).measurable))

lemma memLp_symmSector {ν r : ℕ} (η : ℂ) {F : FockSectorDom ν r → ℂ}
    (hF : MemLp F 2 (fockSectorMeasure ν r)) :
    MemLp (symmSector ν r η F) 2 (fockSectorMeasure ν r) := by
  unfold symmSector
  refine MemLp.const_mul ?_ _
  refine memLp_finsetSum Finset.univ (fun π _ => ?_)
  exact (hF.comp_measurePreserving (measurePreserving_fockSectorPermEquiv ν r π)).const_mul _

theorem inner_symmSector_eq {ν r : ℕ} {η : ℂ} (hη : η = 1 ∨ η = -1)
    {F₁ F₂ : FockSectorDom ν r → ℂ}
    (hF₁ : MemLp F₁ 2 (fockSectorMeasure ν r))
    (hF₂ : MemLp F₂ 2 (fockSectorMeasure ν r)) :
    (∫ x : FockSectorDom ν r,
      star (symmSector ν r η F₁ x) * symmSector ν r η F₂ x ∂(fockSectorMeasure ν r)) =
    ∑ σ : Equiv.Perm (Fin r), η ^ permInversions σ *
      ∫ x : FockSectorDom ν r,
        star (F₁ x) * F₂ (x.1 ∘ σ.symm, x.2 ∘ σ.symm) ∂(fockSectorMeasure ν r) := by
  let c : ℝ := ((r.factorial : ℝ).sqrt)⁻¹
  have hc_sq : (c : ℂ) * (c : ℂ) = (((r.factorial : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    dsimp [c]
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  have h_int_pair : ∀ (π₁ π₂ : Equiv.Perm (Fin r)),
      Integrable (fun x : FockSectorDom ν r =>
        star (η ^ permInversions π₁ * F₁ (fockSectorPermEquiv ν r π₁ x)) *
          (η ^ permInversions π₂ * F₂ (fockSectorPermEquiv ν r π₂ x)))
        (fockSectorMeasure ν r) := by
    intro π₁ π₂
    have hm1 := (hF₁.comp_measurePreserving
      (measurePreserving_fockSectorPermEquiv ν r π₁)).const_mul (η ^ permInversions π₁)
    have hm2 := (hF₂.comp_measurePreserving
      (measurePreserving_fockSectorPermEquiv ν r π₂)).const_mul (η ^ permInversions π₂)
    have hi := L2.integrable_inner (𝕜 := ℂ) (hm1.toLp _) (hm2.toLp _)
    refine hi.congr ?_
    filter_upwards [hm1.coeFn_toLp, hm2.coeFn_toLp] with x hx1 hx2
    rw [RCLike.inner_apply, hx1, hx2]
    simp [mul_comm]
  have h_expand :
      (fun x : FockSectorDom ν r =>
        star (symmSector ν r η F₁ x) * symmSector ν r η F₂ x) =
      fun x => (((r.factorial : ℝ)⁻¹ : ℝ) : ℂ) *
        ∑ π₁ : Equiv.Perm (Fin r), ∑ π₂ : Equiv.Perm (Fin r),
          star (η ^ permInversions π₁ * F₁ (fockSectorPermEquiv ν r π₁ x)) *
            (η ^ permInversions π₂ * F₂ (fockSectorPermEquiv ν r π₂ x)) := by
    ext x
    simp only [symmSector]
    have hstar_c : star (((r.factorial : ℝ).sqrt⁻¹ : ℝ) : ℂ) =
        (((r.factorial : ℝ).sqrt⁻¹ : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal]
    rw [star_mul', hstar_c, star_sum, Finset.mul_sum, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun π₁ _ => ?_)
    refine Finset.sum_congr rfl (fun π₂ _ => ?_)
    have hmul :
        (((r.factorial : ℝ).sqrt⁻¹ : ℝ) : ℂ) * (((r.factorial : ℝ).sqrt⁻¹ : ℝ) : ℂ) =
          (((r.factorial : ℝ)⁻¹ : ℝ) : ℂ) := hc_sq
    calc (((r.factorial : ℝ).sqrt⁻¹ : ℝ) : ℂ) *
            star (η ^ permInversions π₁ * F₁ (fockSectorPermEquiv ν r π₁ x)) *
            ((((r.factorial : ℝ).sqrt⁻¹ : ℝ) : ℂ) *
              (η ^ permInversions π₂ * F₂ (fockSectorPermEquiv ν r π₂ x)))
        = ((((r.factorial : ℝ).sqrt⁻¹ : ℝ) : ℂ) * (((r.factorial : ℝ).sqrt⁻¹ : ℝ) : ℂ)) *
            (star (η ^ permInversions π₁ * F₁ (fockSectorPermEquiv ν r π₁ x)) *
              (η ^ permInversions π₂ * F₂ (fockSectorPermEquiv ν r π₂ x))) := by ring
      _ = _ := by rw [hmul]
  rw [h_expand, integral_const_mul,
    integral_finsetSum Finset.univ (fun π₁ _ =>
      integrable_finsetSum Finset.univ (fun π₂ _ => h_int_pair π₁ π₂))]
  have h_each : ∀ π₁ : Equiv.Perm (Fin r),
      (∫ x : FockSectorDom ν r,
        ∑ π₂ : Equiv.Perm (Fin r),
          star (η ^ permInversions π₁ * F₁ (fockSectorPermEquiv ν r π₁ x)) *
            (η ^ permInversions π₂ * F₂ (fockSectorPermEquiv ν r π₂ x))
        ∂(fockSectorMeasure ν r)) =
      ∑ σ : Equiv.Perm (Fin r), η ^ permInversions σ *
        ∫ x : FockSectorDom ν r,
          star (F₁ x) * F₂ (x.1 ∘ σ.symm, x.2 ∘ σ.symm) ∂(fockSectorMeasure ν r) := by
    intro π₁
    rw [integral_finsetSum Finset.univ (fun π₂ _ => h_int_pair π₁ π₂)]
    rw [← Fintype.sum_equiv (Equiv.mulLeft π₁) _ _ (fun _ => rfl)]
    rw [← Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin r))) _ _ (fun _ => rfl)]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    change (∫ x : FockSectorDom ν r,
        star (η ^ permInversions π₁ * F₁ (fockSectorPermEquiv ν r π₁ x)) *
          (η ^ permInversions (π₁ * σ⁻¹) *
            F₂ (fockSectorPermEquiv ν r (π₁ * σ⁻¹) x))
        ∂(fockSectorMeasure ν r)) = _
    have h_sign :
        star (η ^ permInversions π₁) * η ^ permInversions (π₁ * σ⁻¹) =
          η ^ permInversions σ := by
      have hp1 : (η ^ permInversions π₁) ^ 2 = 1 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul, eta_sq_eq_one hη, one_pow]
      rw [star_eta_pow hη, eta_pow_permInversions_mul hη π₁ σ⁻¹,
        eta_pow_permInversions_inv hη σ, ← mul_assoc, ← pow_two, hp1, one_mul]
    have h_pull :
        (∫ x : FockSectorDom ν r,
          star (η ^ permInversions π₁ * F₁ (fockSectorPermEquiv ν r π₁ x)) *
            (η ^ permInversions (π₁ * σ⁻¹) *
              F₂ (fockSectorPermEquiv ν r (π₁ * σ⁻¹) x))
          ∂(fockSectorMeasure ν r)) =
        η ^ permInversions σ *
          ∫ y : FockSectorDom ν r,
            star (F₁ y) * F₂ (fockSectorPermEquiv ν r σ⁻¹ y) ∂(fockSectorMeasure ν r) := by
      have h_alg :
          (fun x : FockSectorDom ν r =>
            star (η ^ permInversions π₁ * F₁ (fockSectorPermEquiv ν r π₁ x)) *
              (η ^ permInversions (π₁ * σ⁻¹) *
                F₂ (fockSectorPermEquiv ν r (π₁ * σ⁻¹) x))) =
          fun x => η ^ permInversions σ *
            ((fun y : FockSectorDom ν r =>
              star (F₁ y) * F₂ (fockSectorPermEquiv ν r σ⁻¹ y))
              (fockSectorPermEquiv ν r π₁ x)) := by
        ext x
        rw [star_mul']
        have hcomp : fockSectorPermEquiv ν r (π₁ * σ⁻¹) x =
            fockSectorPermEquiv ν r σ⁻¹ (fockSectorPermEquiv ν r π₁ x) := by
          rcases x with ⟨k, s⟩
          simp only [fockSectorPermEquiv_apply]
          rfl
        rw [hcomp]
        calc star (η ^ permInversions π₁) * star (F₁ (fockSectorPermEquiv ν r π₁ x)) *
              (η ^ permInversions (π₁ * σ⁻¹) *
                F₂ (fockSectorPermEquiv ν r σ⁻¹ (fockSectorPermEquiv ν r π₁ x)))
            = (star (η ^ permInversions π₁) * η ^ permInversions (π₁ * σ⁻¹)) *
                (star (F₁ (fockSectorPermEquiv ν r π₁ x)) *
                  F₂ (fockSectorPermEquiv ν r σ⁻¹ (fockSectorPermEquiv ν r π₁ x))) := by ring
          _ = _ := by rw [h_sign]
      rw [h_alg, integral_const_mul]
      congr 1
      exact (measurePreserving_fockSectorPermEquiv ν r π₁).integral_comp
        (fockSectorPermEquiv ν r π₁).measurableEmbedding
        (fun y : FockSectorDom ν r => star (F₁ y) * F₂ (fockSectorPermEquiv ν r σ⁻¹ y))
    rw [h_pull]
    rfl
  simp_rw [h_each, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [nsmul_eq_mul, ← mul_assoc]
  have hfact_ne : ((r.factorial : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r))
  have hmul_inv : (((r.factorial : ℝ)⁻¹ : ℝ) : ℂ) * ((r.factorial : ℕ) : ℂ) = 1 := by
    push_cast
    exact inv_mul_cancel₀ hfact_ne
  rw [hmul_inv, one_mul]

namespace PartialPairing

noncomputable def partialMomentum {n r : ℕ} (m : ℝ) (L : PartialPairing n r)
    (p_int : L.InternalChord → Fin 3 → ℝ) (k_ext : Fin r → Fin 3 → ℝ) :
    Fin n → Fin 4 → ℝ :=
  fun i => match L.partialSlotEquiv.symm i with
    | Sum.inl a => -massShellVec m (k_ext a)
    | Sum.inr (c, 0) => massShellVec m (p_int c)
    | Sum.inr (c, 1) => -massShellVec m (p_int c)

@[simp]
lemma partialMomentum_unpaired {n r : ℕ} (m : ℝ) (L : PartialPairing n r)
    (p_int : L.InternalChord → Fin 3 → ℝ) (k_ext : Fin r → Fin 3 → ℝ) (a : Fin r) :
    L.partialMomentum m p_int k_ext (L.unpaired a) = -massShellVec m (k_ext a) := by
  have hsym : L.partialSlotEquiv.symm (L.unpaired a) = Sum.inl a :=
    L.partialSlotEquiv.symm_apply_eq.mpr rfl
  unfold partialMomentum
  rw [hsym]

@[simp]
lemma partialMomentum_fst {n r : ℕ} (m : ℝ) (L : PartialPairing n r)
    (p_int : L.InternalChord → Fin 3 → ℝ) (k_ext : Fin r → Fin 3 → ℝ) (c : L.InternalChord) :
    L.partialMomentum m p_int k_ext c.1 = massShellVec m (p_int c) := by
  have hsym : L.partialSlotEquiv.symm c.1 = Sum.inr (c, 0) :=
    L.partialSlotEquiv.symm_apply_eq.mpr rfl
  unfold partialMomentum
  rw [hsym]

@[simp]
lemma partialMomentum_mate {n r : ℕ} (m : ℝ) (L : PartialPairing n r)
    (p_int : L.InternalChord → Fin 3 → ℝ) (k_ext : Fin r → Fin 3 → ℝ) (c : L.InternalChord) :
    L.partialMomentum m p_int k_ext (L.mate c.1) = -massShellVec m (p_int c) := by
  have hsym : L.partialSlotEquiv.symm (L.mate c.1) = Sum.inr (c, 1) :=
    L.partialSlotEquiv.symm_apply_eq.mpr rfl
  unfold partialMomentum
  rw [hsym]

lemma continuous_partialMomentum_uncurry {n r : ℕ} (m : ℝ) (L : PartialPairing n r) :
    Continuous (fun pk : (L.InternalChord → Fin 3 → ℝ) × (Fin r → Fin 3 → ℝ) =>
      L.partialMomentum m pk.1 pk.2) := by
  refine continuous_pi (fun i => ?_)
  unfold partialMomentum
  rcases h : L.partialSlotEquiv.symm i with a | ⟨c, s⟩
  · exact ((continuous_massShellVec m).comp ((continuous_apply a).comp continuous_snd)).neg
  · fin_cases s
    · exact (continuous_massShellVec m).comp ((continuous_apply c).comp continuous_fst)
    · exact ((continuous_massShellVec m).comp ((continuous_apply c).comp continuous_fst)).neg

lemma measurable_partialMomentum_uncurry {n r : ℕ} (m : ℝ) (L : PartialPairing n r) :
    Measurable (fun pk : (L.InternalChord → Fin 3 → ℝ) × (Fin r → Fin 3 → ℝ) =>
      L.partialMomentum m pk.1 pk.2) :=
  (L.continuous_partialMomentum_uncurry m).measurable

lemma one_add_norm_internal_le_momentumToEuclid {n r : ℕ} (m : ℝ) (L : PartialPairing n r)
    (p_int : L.InternalChord → Fin 3 → ℝ) (k_ext : Fin r → Fin 3 → ℝ) (c : L.InternalChord) :
    1 + ‖p_int c‖ ≤
      (2 * Real.pi) * (1 + ‖momentumToEuclidCLMN n (L.partialMomentum m p_int k_ext)‖) := by
  let u := momentumToEuclidCLMN n (L.partialMomentum m p_int k_ext)
  have hpi : 0 < 2 * Real.pi := by positivity
  have hp_norm : ‖p_int c‖ ≤ (2 * Real.pi) * ‖u‖ := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hpi.le (norm_nonneg u))).mpr (fun j => ?_)
    have hu_coord : u (c.1, j.succ) = (2 * Real.pi)⁻¹ * p_int c j := by
      have hu_app :
          u (c.1, j.succ) = (2 * Real.pi)⁻¹ * L.partialMomentum m p_int k_ext c.1 j.succ := by
        dsimp only [u, momentumToEuclidCLMN, posScaledMomentumCLMN, posScaledMomentumN,
          piSpaceEquiv, finCurryEquiv, finEuclidEquiv]
        simp
      rw [hu_app, L.partialMomentum_fst]
      fin_cases j <;> simp [massShellVec]
    have hpj : p_int c j = (2 * Real.pi) * u (c.1, j.succ) := by
      rw [hu_coord]
      field_simp [hpi.ne']
    calc ‖p_int c j‖ = ‖(2 * Real.pi) * u (c.1, j.succ)‖ := by rw [hpj]
      _ = (2 * Real.pi) * ‖u (c.1, j.succ)‖ := by
          rw [norm_mul, Real.norm_of_nonneg hpi.le]
      _ ≤ (2 * Real.pi) * ‖u‖ :=
          mul_le_mul_of_nonneg_left (PiLp.norm_apply_le u (c.1, j.succ)) hpi.le
  have hpi1 : 1 ≤ 2 * Real.pi := by
    have := Real.pi_gt_three
    linarith
  linarith

lemma one_add_norm_unpaired_le_momentumToEuclid {n r : ℕ} (m : ℝ) (L : PartialPairing n r)
    (p_int : L.InternalChord → Fin 3 → ℝ) (k_ext : Fin r → Fin 3 → ℝ) (a : Fin r) :
    1 + ‖k_ext a‖ ≤
      (2 * Real.pi) * (1 + ‖momentumToEuclidCLMN n (L.partialMomentum m p_int k_ext)‖) := by
  let u := momentumToEuclidCLMN n (L.partialMomentum m p_int k_ext)
  have hpi : 0 < 2 * Real.pi := by positivity
  have hp_norm : ‖k_ext a‖ ≤ (2 * Real.pi) * ‖u‖ := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hpi.le (norm_nonneg u))).mpr (fun j => ?_)
    have hu_coord : u (L.unpaired a, j.succ) = -((2 * Real.pi)⁻¹ * k_ext a j) := by
      have hu_app :
          u (L.unpaired a, j.succ) =
            (2 * Real.pi)⁻¹ * L.partialMomentum m p_int k_ext (L.unpaired a) j.succ := by
        dsimp only [u, momentumToEuclidCLMN, posScaledMomentumCLMN, posScaledMomentumN,
          piSpaceEquiv, finCurryEquiv, finEuclidEquiv]
        simp
      rw [hu_app, L.partialMomentum_unpaired]
      fin_cases j <;> simp [massShellVec]
    have hpj : k_ext a j = -((2 * Real.pi) * u (L.unpaired a, j.succ)) := by
      rw [hu_coord]
      field_simp [hpi.ne']
    calc ‖k_ext a j‖ = ‖-((2 * Real.pi) * u (L.unpaired a, j.succ))‖ := by rw [hpj]
      _ = (2 * Real.pi) * ‖u (L.unpaired a, j.succ)‖ := by
          rw [norm_neg, norm_mul, Real.norm_of_nonneg hpi.le]
      _ ≤ (2 * Real.pi) * ‖u‖ :=
          mul_le_mul_of_nonneg_left (PiLp.norm_apply_le u (L.unpaired a, j.succ)) hpi.le
  have hpi1 : 1 ≤ 2 * Real.pi := by
    have := Real.pi_gt_three
    linarith
  linarith

theorem norm_schwartz_momentumToEuclid_partial_le {n r : ℕ} (m : ℝ) (L : PartialPairing n r)
    (g : SchwartzMap (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ)
    (p_int : L.InternalChord → Fin 3 → ℝ) (k_ext : Fin r → Fin 3 → ℝ) :
    ‖g (momentumToEuclidCLMN n (L.partialMomentum m p_int k_ext))‖ ≤
      ((4 * Real.pi) ^ (4 * (Fintype.card L.InternalChord + r)) *
        ((Finset.Iic (4 * (Fintype.card L.InternalChord + r), 0)).sup
          (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ) g)) *
        (∏ c : L.InternalChord, ((1 + ‖p_int c‖) ^ 4)⁻¹) *
        (∏ a : Fin r, ((1 + ‖k_ext a‖) ^ 4)⁻¹) := by
  let d := Fintype.card L.InternalChord + r
  let u := momentumToEuclidCLMN n (L.partialMomentum m p_int k_ext)
  let S_sem : ℝ := (Finset.Iic (4 * d, 0)).sup
    (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ) g
  have h_sch : (1 + ‖u‖) ^ (4 * d) * ‖g u‖ ≤ 2 ^ (4 * d) * S_sem := by
    have h0 := SchwartzMap.one_add_le_sup_seminorm_apply
      (𝕜 := ℂ) (m := (4 * d, 0)) (k := 4 * d) (n := 0) le_rfl le_rfl g u
    have h_fam :
        (fun m : ℕ × ℕ =>
          SchwartzMap.seminorm (E := EuclideanSpace ℝ (Fin n × Fin 4)) (F := ℂ) ℂ m.1 m.2) =
        schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ := rfl
    simpa [norm_iteratedFDeriv_zero, h_fam, S_sem] using h0
  have h_prod_c :
      (∏ c : L.InternalChord, (1 + ‖p_int c‖) ^ 4) ≤
        ((2 * Real.pi) * (1 + ‖u‖)) ^ (4 * Fintype.card L.InternalChord) := by
    calc (∏ c : L.InternalChord, (1 + ‖p_int c‖) ^ 4)
        ≤ ∏ _c : L.InternalChord, ((2 * Real.pi) * (1 + ‖u‖)) ^ 4 :=
          Finset.prod_le_prod (fun _ _ => by positivity)
            (fun c _ => pow_le_pow_left₀ (by positivity)
              (L.one_add_norm_internal_le_momentumToEuclid m p_int k_ext c) 4)
      _ = (((2 * Real.pi) * (1 + ‖u‖)) ^ 4) ^ Fintype.card L.InternalChord := by
          rw [Finset.prod_const, Finset.card_univ]
      _ = ((2 * Real.pi) * (1 + ‖u‖)) ^ (4 * Fintype.card L.InternalChord) :=
          (pow_mul _ 4 _).symm
  have h_prod_a :
      (∏ a : Fin r, (1 + ‖k_ext a‖) ^ 4) ≤ ((2 * Real.pi) * (1 + ‖u‖)) ^ (4 * r) := by
    calc (∏ a : Fin r, (1 + ‖k_ext a‖) ^ 4)
        ≤ ∏ _a : Fin r, ((2 * Real.pi) * (1 + ‖u‖)) ^ 4 :=
          Finset.prod_le_prod (fun _ _ => by positivity)
            (fun a _ => pow_le_pow_left₀ (by positivity)
              (L.one_add_norm_unpaired_le_momentumToEuclid m p_int k_ext a) 4)
      _ = (((2 * Real.pi) * (1 + ‖u‖)) ^ 4) ^ r := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = ((2 * Real.pi) * (1 + ‖u‖)) ^ (4 * r) := (pow_mul _ 4 r).symm
  have h_prod_both :
      ((∏ c : L.InternalChord, (1 + ‖p_int c‖) ^ 4) * (∏ a : Fin r, (1 + ‖k_ext a‖) ^ 4)) ≤
        (2 * Real.pi) ^ (4 * d) * (1 + ‖u‖) ^ (4 * d) := by
    calc ((∏ c : L.InternalChord, (1 + ‖p_int c‖) ^ 4) * (∏ a : Fin r, (1 + ‖k_ext a‖) ^ 4))
        ≤ ((2 * Real.pi) * (1 + ‖u‖)) ^ (4 * Fintype.card L.InternalChord) *
            ((2 * Real.pi) * (1 + ‖u‖)) ^ (4 * r) :=
          mul_le_mul h_prod_c h_prod_a
            (Finset.prod_nonneg (fun _ _ => by positivity)) (by positivity)
      _ = ((2 * Real.pi) * (1 + ‖u‖)) ^ (4 * d) := by
          rw [← pow_add]
          congr 1
          dsimp [d]
          ring
      _ = (2 * Real.pi) ^ (4 * d) * (1 + ‖u‖) ^ (4 * d) := mul_pow _ _ (4 * d)
  have h_prod :
      ((∏ c : L.InternalChord, (1 + ‖p_int c‖) ^ 4) * (∏ a : Fin r, (1 + ‖k_ext a‖) ^ 4)) *
        ‖g u‖ ≤ (4 * Real.pi) ^ (4 * d) * S_sem := by
    calc ((∏ c : L.InternalChord, (1 + ‖p_int c‖) ^ 4) * (∏ a : Fin r, (1 + ‖k_ext a‖) ^ 4)) *
          ‖g u‖
        ≤ ((2 * Real.pi) ^ (4 * d) * (1 + ‖u‖) ^ (4 * d)) * ‖g u‖ :=
          mul_le_mul_of_nonneg_right h_prod_both (norm_nonneg _)
      _ = (2 * Real.pi) ^ (4 * d) * ((1 + ‖u‖) ^ (4 * d) * ‖g u‖) := by ring
      _ ≤ (2 * Real.pi) ^ (4 * d) * (2 ^ (4 * d) * S_sem) :=
          mul_le_mul_of_nonneg_left h_sch (by positivity)
      _ = ((2 * Real.pi) * 2) ^ (4 * d) * S_sem := by rw [← mul_assoc, ← mul_pow]
      _ = (4 * Real.pi) ^ (4 * d) * S_sem := by congr 2; ring
  have h_pos :
      0 < (∏ c : L.InternalChord, (1 + ‖p_int c‖) ^ 4) * (∏ a : Fin r, (1 + ‖k_ext a‖) ^ 4) :=
    mul_pos (Finset.prod_pos (fun _ _ => by positivity))
      (Finset.prod_pos (fun _ _ => by positivity))
  rw [mul_assoc (_ * S_sem), Finset.prod_inv_distrib, Finset.prod_inv_distrib, ← mul_inv]
  exact (le_mul_inv_iff₀' h_pos).mpr h_prod

def concatRevParamEquiv {j k r : ℕ} (L : PartialPairing j r) (R : PartialPairing k r)
    (σ : Equiv.Perm (Fin r)) :
    (((L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ)) ×
      (Fin r → Fin 3 → ℝ)) ≃ᵐ
      ((concatRev L R σ).Chord → Fin 3 → ℝ) :=
  (((MeasurableEquiv.sumPiEquivProdPi
      (fun _ : L.InternalChord ⊕ R.InternalChord => Fin 3 → ℝ)).symm.prodCongr
      (MeasurableEquiv.refl (Fin r → Fin 3 → ℝ))).trans
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : (L.InternalChord ⊕ R.InternalChord) ⊕ Fin r => Fin 3 → ℝ)).symm).trans
    (MeasurableEquiv.piCongrLeft
      (fun _ : (concatRev L R σ).Chord => Fin 3 → ℝ)
      (concatRevChordEquiv L R σ))

lemma measurePreserving_concatRevParamEquiv {j k r : ℕ}
    (L : PartialPairing j r) (R : PartialPairing k r) (σ : Equiv.Perm (Fin r)) :
    MeasurePreserving (concatRevParamEquiv L R σ) volume volume := by
  unfold concatRevParamEquiv
  exact (((volume_measurePreserving_sumPiEquivProdPi_symm
      (fun _ : L.InternalChord ⊕ R.InternalChord => Fin 3 → ℝ)).prod
      (MeasurePreserving.id volume)).trans
    (volume_measurePreserving_sumPiEquivProdPi_symm
      (fun _ : (L.InternalChord ⊕ R.InternalChord) ⊕ Fin r => Fin 3 → ℝ))).trans
    (volume_measurePreserving_piCongrLeft
      (fun _ : (concatRev L R σ).Chord => Fin 3 → ℝ)
      (concatRevChordEquiv L R σ))

@[simp]
lemma concatRevParamEquiv_apply_inl_inl {j k r : ℕ}
    (L : PartialPairing j r) (R : PartialPairing k r) (σ : Equiv.Perm (Fin r))
    (p_L : L.InternalChord → Fin 3 → ℝ) (p_R : R.InternalChord → Fin 3 → ℝ)
    (k_ext : Fin r → Fin 3 → ℝ) (cL : L.InternalChord) :
    concatRevParamEquiv L R σ ((p_L, p_R), k_ext)
      (concatRevChordEquiv L R σ (Sum.inl (Sum.inl cL))) = p_L cL := by
  unfold concatRevParamEquiv
  simp only [MeasurableEquiv.trans_apply, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_apply]
  rfl

@[simp]
lemma concatRevParamEquiv_apply_inl_inr {j k r : ℕ}
    (L : PartialPairing j r) (R : PartialPairing k r) (σ : Equiv.Perm (Fin r))
    (p_L : L.InternalChord → Fin 3 → ℝ) (p_R : R.InternalChord → Fin 3 → ℝ)
    (k_ext : Fin r → Fin 3 → ℝ) (cR : R.InternalChord) :
    concatRevParamEquiv L R σ ((p_L, p_R), k_ext)
      (concatRevChordEquiv L R σ (Sum.inl (Sum.inr cR))) = p_R cR := by
  unfold concatRevParamEquiv
  simp only [MeasurableEquiv.trans_apply, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_apply]
  rfl

@[simp]
lemma concatRevParamEquiv_apply_inr {j k r : ℕ}
    (L : PartialPairing j r) (R : PartialPairing k r) (σ : Equiv.Perm (Fin r))
    (p_L : L.InternalChord → Fin 3 → ℝ) (p_R : R.InternalChord → Fin 3 → ℝ)
    (k_ext : Fin r → Fin 3 → ℝ) (a : Fin r) :
    concatRevParamEquiv L R σ ((p_L, p_R), k_ext)
      (concatRevChordEquiv L R σ (Sum.inr a)) = k_ext a := by
  unfold concatRevParamEquiv
  simp only [MeasurableEquiv.trans_apply, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_apply]
  rfl

lemma concatRev_momentum_left {j k r : ℕ} (m : ℝ)
    (L : PartialPairing j r) (R : PartialPairing k r) (σ : Equiv.Perm (Fin r))
    (p_L : L.InternalChord → Fin 3 → ℝ) (p_R : R.InternalChord → Fin 3 → ℝ)
    (k_ext : Fin r → Fin 3 → ℝ) :
    (fun i : Fin j =>
      -(concatRev L R σ).momentum m (concatRevParamEquiv L R σ ((p_L, p_R), k_ext))
        (Fin.castAdd k (Fin.rev i))) =
      L.partialMomentum m p_L k_ext := by
  funext i
  rcases L.partialSlotEquiv.surjective i with ⟨a | ⟨cL, s⟩, rfl⟩
  · have hslot : L.partialSlotEquiv (Sum.inl a) = L.unpaired a := rfl
    rw [hslot, L.partialMomentum_unpaired]
    have hc : Fin.castAdd k (Fin.rev (L.unpaired a)) =
        (concatRevChordEquiv L R σ (Sum.inr a)).1 := rfl
    rw [hc, ChordPairing.momentum_apply_fst, concatRevParamEquiv_apply_inr]
  · have hs : s = 0 ∨ s = 1 := by fin_cases s <;> simp
    rcases hs with rfl | rfl
    · have hslot : L.partialSlotEquiv (Sum.inr (cL, 0)) = cL.1 := rfl
      rw [hslot, L.partialMomentum_fst]
      have hmate : (concatRev L R σ).mate
          (concatRevChordEquiv L R σ (Sum.inl (Sum.inl cL))).1 =
          Fin.castAdd k (Fin.rev cL.1) := by
        change (concatRev L R σ).mate (concatSlotEquiv j k (Sum.inl (L.mate cL.1))) =
          concatSlotEquiv j k (Sum.inl cL.1)
        rw [concatRev_mate_slot]
        dsimp [concatSumFun]
        rw [dif_neg (L.mate_mate_ne_of_internalChord cL), L.mate_mate]
      rw [← hmate, ChordPairing.momentum_apply_mate, concatRevParamEquiv_apply_inl_inl, neg_neg]
    · have hslot : L.partialSlotEquiv (Sum.inr (cL, 1)) = L.mate cL.1 := rfl
      rw [hslot, L.partialMomentum_mate]
      have hc : Fin.castAdd k (Fin.rev (L.mate cL.1)) =
          (concatRevChordEquiv L R σ (Sum.inl (Sum.inl cL))).1 := rfl
      rw [hc, ChordPairing.momentum_apply_fst, concatRevParamEquiv_apply_inl_inl]

lemma concatRev_momentum_right {j k r : ℕ} (m : ℝ)
    (L : PartialPairing j r) (R : PartialPairing k r) (σ : Equiv.Perm (Fin r))
    (p_L : L.InternalChord → Fin 3 → ℝ) (p_R : R.InternalChord → Fin 3 → ℝ)
    (k_ext : Fin r → Fin 3 → ℝ) :
    (fun t : Fin k =>
      (concatRev L R σ).momentum m (concatRevParamEquiv L R σ ((p_L, p_R), k_ext))
        (Fin.natAdd j t)) =
      R.partialMomentum m p_R (k_ext ∘ σ.symm) := by
  funext t
  rcases R.partialSlotEquiv.surjective t with ⟨b | ⟨cR, s⟩, rfl⟩
  · have hslot : R.partialSlotEquiv (Sum.inl b) = R.unpaired b := rfl
    rw [hslot, R.partialMomentum_unpaired]
    have hmate : (concatRev L R σ).mate
        (concatRevChordEquiv L R σ (Sum.inr (σ.symm b))).1 =
        Fin.natAdd j (R.unpaired b) := by
      change (concatRev L R σ).mate (concatSlotEquiv j k (Sum.inl (L.unpaired (σ.symm b)))) =
        concatSlotEquiv j k (Sum.inr (R.unpaired b))
      rw [concatRev_mate_slot]
      dsimp [concatSumFun]
      rw [dif_pos (L.mate_unpaired _), L.unpairedIdx_unpaired, σ.apply_symm_apply]
    rw [← hmate, ChordPairing.momentum_apply_mate, concatRevParamEquiv_apply_inr]
    rfl
  · have hs : s = 0 ∨ s = 1 := by fin_cases s <;> simp
    rcases hs with rfl | rfl
    · have hslot : R.partialSlotEquiv (Sum.inr (cR, 0)) = cR.1 := rfl
      rw [hslot, R.partialMomentum_fst]
      have hc : Fin.natAdd j cR.1 =
          (concatRevChordEquiv L R σ (Sum.inl (Sum.inr cR))).1 := rfl
      rw [hc, ChordPairing.momentum_apply_fst, concatRevParamEquiv_apply_inl_inr]
    · have hslot : R.partialSlotEquiv (Sum.inr (cR, 1)) = R.mate cR.1 := rfl
      rw [hslot, R.partialMomentum_mate]
      have hmate : (concatRev L R σ).mate
          (concatRevChordEquiv L R σ (Sum.inl (Sum.inr cR))).1 =
          Fin.natAdd j (R.mate cR.1) := by
        change (concatRev L R σ).mate (concatSlotEquiv j k (Sum.inr cR.1)) =
          concatSlotEquiv j k (Sum.inr (R.mate cR.1))
        rw [concatRev_mate_slot]
        dsimp [concatSumFun]
        rw [dif_neg (R.mate_ne_self_of_internalChord cR)]
      rw [← hmate, ChordPairing.momentum_apply_mate, concatRevParamEquiv_apply_inl_inr]

lemma wickChordWeight_concatRev_aux {ι : Type*} {j k r : ℕ} (m : ℝ)
    (C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ)
    (L : PartialPairing j r) (R : PartialPairing k r) (σ : Equiv.Perm (Fin r))
    (β : Fin j → ι) (α' : Fin k → ι)
    (p : (concatRev L R σ).Chord → Fin 3 → ℝ) :
    wickChordWeight m C (concatRev L R σ) (Fin.append (β ∘ Fin.rev) α') p =
      (∏ cL : L.InternalChord,
        massShellWeight m C (![β cL.1, β (L.mate cL.1)] ∘ Fin.rev)
          (p (concatRevChordEquiv L R σ (Sum.inl (Sum.inl cL))))) *
      (∏ cR : R.InternalChord,
        massShellWeight m C ![α' cR.1, α' (R.mate cR.1)]
          (p (concatRevChordEquiv L R σ (Sum.inl (Sum.inr cR))))) *
      (∏ a : Fin r,
        massShellWeight m C ![β (L.unpaired a), α' (R.unpaired (σ a))]
          (p (concatRevChordEquiv L R σ (Sum.inr a)))) := by
  have h_inl : ∀ i : Fin j,
      Fin.append (β ∘ Fin.rev) α' (concatSlotEquiv j k (Sum.inl i)) = β i := by
    intro i
    change Fin.append (β ∘ Fin.rev) α' (Fin.castAdd k (Fin.rev i)) = β i
    rw [Fin.append_left]
    simp [Fin.rev_rev]
  have h_inr : ∀ t : Fin k,
      Fin.append (β ∘ Fin.rev) α' (concatSlotEquiv j k (Sum.inr t)) = α' t := by
    intro t
    change Fin.append (β ∘ Fin.rev) α' (Fin.natAdd j t) = α' t
    rw [Fin.append_right]
  unfold wickChordWeight
  rw [← (concatRevChordEquiv L R σ).prod_comp, Fintype.prod_sum_type, Fintype.prod_sum_type]
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ ?_) ?_
  · refine Finset.prod_congr rfl (fun cL _ => ?_)
    have hc1 : (concatRevChordEquiv L R σ (Sum.inl (Sum.inl cL))).1 =
        concatSlotEquiv j k (Sum.inl (L.mate cL.1)) := rfl
    have hcm : (concatRev L R σ).mate (concatRevChordEquiv L R σ (Sum.inl (Sum.inl cL))).1 =
        concatSlotEquiv j k (Sum.inl cL.1) := by
      rw [hc1, concatRev_mate_slot]
      dsimp [concatSumFun]
      rw [dif_neg (L.mate_mate_ne_of_internalChord cL), L.mate_mate]
    have h_vec :
        ![Fin.append (β ∘ Fin.rev) α' (concatRevChordEquiv L R σ (Sum.inl (Sum.inl cL))).1,
          Fin.append (β ∘ Fin.rev) α'
            ((concatRev L R σ).mate (concatRevChordEquiv L R σ (Sum.inl (Sum.inl cL))).1)] =
        ![β cL.1, β (L.mate cL.1)] ∘ Fin.rev := by
      rw [hcm, hc1, h_inl, h_inl]
      ext s
      fin_cases s <;> rfl
    rw [h_vec]
  · refine Finset.prod_congr rfl (fun cR _ => ?_)
    have hc1 : (concatRevChordEquiv L R σ (Sum.inl (Sum.inr cR))).1 =
        concatSlotEquiv j k (Sum.inr cR.1) := rfl
    have hcm : (concatRev L R σ).mate (concatRevChordEquiv L R σ (Sum.inl (Sum.inr cR))).1 =
        concatSlotEquiv j k (Sum.inr (R.mate cR.1)) := by
      rw [hc1, concatRev_mate_slot]
      dsimp [concatSumFun]
      rw [dif_neg (R.mate_ne_self_of_internalChord cR)]
    rw [hcm, hc1, h_inr, h_inr]
  · refine Finset.prod_congr rfl (fun a _ => ?_)
    have hc1 : (concatRevChordEquiv L R σ (Sum.inr a)).1 =
        concatSlotEquiv j k (Sum.inl (L.unpaired a)) := rfl
    have hcm : (concatRev L R σ).mate (concatRevChordEquiv L R σ (Sum.inr a)).1 =
        concatSlotEquiv j k (Sum.inr (R.unpaired (σ a))) := by
      rw [hc1, concatRev_mate_slot]
      dsimp [concatSumFun]
      rw [dif_pos (L.mate_unpaired a), L.unpairedIdx_unpaired]
    rw [hcm, hc1, h_inl, h_inr]

lemma wickChordWeight_concatRev {ι : Type*} {j k r : ℕ} (m : ℝ)
    (C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ)
    (L : PartialPairing j r) (R : PartialPairing k r) (σ : Equiv.Perm (Fin r))
    (β : Fin j → ι) (α' : Fin k → ι)
    (p_L : L.InternalChord → Fin 3 → ℝ) (p_R : R.InternalChord → Fin 3 → ℝ)
    (k_ext : Fin r → Fin 3 → ℝ) :
    wickChordWeight m C (concatRev L R σ) (Fin.append (β ∘ Fin.rev) α')
        (concatRevParamEquiv L R σ ((p_L, p_R), k_ext)) =
      (∏ cL : L.InternalChord,
        massShellWeight m C (![β cL.1, β (L.mate cL.1)] ∘ Fin.rev) (p_L cL)) *
      (∏ cR : R.InternalChord,
        massShellWeight m C ![α' cR.1, α' (R.mate cR.1)] (p_R cR)) *
      (∏ a : Fin r,
        massShellWeight m C ![β (L.unpaired a), α' (R.unpaired (σ a))] (k_ext a)) := by
  rw [wickChordWeight_concatRev_aux]
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ ?_) ?_
  · refine Finset.prod_congr rfl (fun cL _ => ?_)
    rw [concatRevParamEquiv_apply_inl_inl]
  · refine Finset.prod_congr rfl (fun cR _ => ?_)
    rw [concatRevParamEquiv_apply_inl_inr]
  · refine Finset.prod_congr rfl (fun a _ => ?_)
    rw [concatRevParamEquiv_apply_inr]

end PartialPairing

structure PartialMomentumBound (m : ℝ) (j : ℕ) (φ : (Fin j → Fin 4 → ℝ) → ℂ) : Prop where
  measurable_φ : Measurable φ
  bound : ∀ (r : ℕ) (L : PartialPairing j r),
    ∃ (K : ℝ) (u : L.InternalChord → (Fin 3 → ℝ) → ℝ) (v : Fin r → (Fin 3 → ℝ) → ℝ),
      0 ≤ K ∧
      (∀ c, Integrable (u c) volume) ∧
      (∀ a, Measurable (v a)) ∧
      (∀ a, Integrable (fun q => (v a q) ^ 2) volume) ∧
      (∀ c q, 0 ≤ u c q) ∧
      (∀ a q, 0 ≤ v a q) ∧
      ∀ (p_int : L.InternalChord → Fin 3 → ℝ) (k_ext : Fin r → Fin 3 → ℝ),
        ‖φ (L.partialMomentum m p_int k_ext)‖ ≤
          K * (∏ c, u c (p_int c)) * (∏ a, v a (k_ext a))

noncomputable def fockPartialIntWeight {ι : Type*} (m : ℝ)
    (C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ) {j r : ℕ} (α : Fin j → ι)
    (L : PartialPairing j r) (p_int : L.InternalChord → Fin 3 → ℝ) : ℂ :=
  ∏ c : L.InternalChord, massShellWeight m C ![α c.1, α (L.mate c.1)] (p_int c)

lemma measurable_fockPartialIntWeight {ι : Type*} {m : ℝ}
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    {j r : ℕ} (α : Fin j → ι) (L : PartialPairing j r) :
    Measurable (fockPartialIntWeight m C α L) :=
  Finset.measurable_prod Finset.univ (fun c _ =>
    (measurable_massShellWeight hC ![α c.1, α (L.mate c.1)]).comp (measurable_pi_apply c))

lemma exists_norm_fockPartialIntWeight_le {ι : Type*} {m : ℝ}
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    {j r : ℕ} (α : Fin j → ι) (L : PartialPairing j r) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p_int : L.InternalChord → Fin 3 → ℝ,
      ‖fockPartialIntWeight m C α L p_int‖ ≤ B := by
  let Bc : L.InternalChord → ℝ := fun c => Classical.choose (hC.2 ![α c.1, α (L.mate c.1)])
  have hBc : ∀ c : L.InternalChord,
      0 ≤ Bc c ∧ ∀ q : Fin 3 → ℝ, ‖massShellWeight m C ![α c.1, α (L.mate c.1)] q‖ ≤ Bc c :=
    fun c => Classical.choose_spec (hC.2 ![α c.1, α (L.mate c.1)])
  refine ⟨∏ c : L.InternalChord, Bc c, Finset.prod_nonneg (fun c _ => (hBc c).1), fun p_int => ?_⟩
  unfold fockPartialIntWeight
  rw [norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun c _ => (hBc c).2 (p_int c))

lemma integrable_fockPartialIntegrand {ι : Type*} {m : ℝ}
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    {j r : ℕ} (α : Fin j → ι) {φ : (Fin j → Fin 4 → ℝ) → ℂ}
    (hφ : PartialMomentumBound m j φ) (L : PartialPairing j r)
    (k_ext : Fin r → Fin 3 → ℝ) :
    Integrable (fun p_int : L.InternalChord → Fin 3 → ℝ =>
      fockPartialIntWeight m C α L p_int * φ (L.partialMomentum m p_int k_ext)) volume := by
  rcases exists_norm_fockPartialIntWeight_le hC α L with ⟨B, hB_nn, hB⟩
  rcases hφ.bound r L with ⟨K, u, v, hK_nn, hu_int, _, _, _, hv_nn, hbound⟩
  let Cv : ℝ := B * K * ∏ a : Fin r, v a (k_ext a)
  have h_dom : Integrable
      (fun p_int : L.InternalChord → Fin 3 → ℝ => Cv * ∏ c : L.InternalChord, u c (p_int c))
      volume :=
    (Integrable.fintype_prod (f := u) hu_int).const_mul Cv
  have h_meas_pm : Measurable (fun p_int : L.InternalChord → Fin 3 → ℝ =>
      L.partialMomentum m p_int k_ext) :=
    (L.continuous_partialMomentum_uncurry m |>.comp
      (continuous_id.prodMk continuous_const)).measurable
  have h_meas : Measurable (fun p_int : L.InternalChord → Fin 3 → ℝ =>
      fockPartialIntWeight m C α L p_int * φ (L.partialMomentum m p_int k_ext)) :=
    (measurable_fockPartialIntWeight hC α L).mul (hφ.measurable_φ.comp h_meas_pm)
  refine h_dom.mono' h_meas.aestronglyMeasurable (Filter.Eventually.of_forall (fun p_int => ?_))
  rw [norm_mul]
  calc ‖fockPartialIntWeight m C α L p_int‖ * ‖φ (L.partialMomentum m p_int k_ext)‖
      ≤ B * (K * (∏ c, u c (p_int c)) * (∏ a, v a (k_ext a))) :=
        mul_le_mul (hB p_int) (hbound p_int k_ext) (norm_nonneg _) hB_nn
    _ = Cv * ∏ c, u c (p_int c) := by dsimp [Cv]; ring

lemma norm_eta_pow {η : ℂ} (hη : η = 1 ∨ η = -1) (n : ℕ) : ‖η ^ n‖ = 1 := by
  rcases hη with rfl | rfl <;> simp

noncomputable def fockPartialTerm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) {j r : ℕ} (α : Fin j → ι)
    (φ : (Fin j → Fin 4 → ℝ) → ℂ) (L : PartialPairing j r)
    (x : FockSectorDom M_mode.ν r) : ℂ :=
  η ^ L.partialCross *
    (∏ a : Fin r, M_mode.w (x.2 a) (x.1 a) (α (L.unpaired a))) *
    ∫ p_int : L.InternalChord → Fin 3 → ℝ,
      fockPartialIntWeight m C α L p_int * φ (L.partialMomentum m p_int x.1)

lemma measurable_fockPartialTerm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    {j r : ℕ} (α : Fin j → ι) {φ : (Fin j → Fin 4 → ℝ) → ℂ}
    (hφ : PartialMomentumBound m j φ) (L : PartialPairing j r) :
    Measurable (fockPartialTerm M_mode α φ L) := by
  have h_w : Measurable (fun x : FockSectorDom M_mode.ν r =>
      ∏ a : Fin r, M_mode.w (x.2 a) (x.1 a) (α (L.unpaired a))) := by
    refine Finset.measurable_prod Finset.univ (fun a _ => ?_)
    have h_sum : ∀ x : FockSectorDom M_mode.ν r,
        M_mode.w (x.2 a) (x.1 a) (α (L.unpaired a)) =
          ∑ s : Fin M_mode.ν,
            (if x.2 a = s then (1 : ℂ) else 0) * M_mode.w s (x.1 a) (α (L.unpaired a)) := by
      intro x
      simp
    simp_rw [h_sum]
    refine Finset.measurable_sum Finset.univ (fun s _ => ?_)
    have h_ind : Measurable (fun x : FockSectorDom M_mode.ν r =>
        if x.2 a = s then (1 : ℂ) else 0) :=
      Measurable.ite
        ((measurableSet_singleton s).preimage ((measurable_pi_apply a).comp measurable_snd))
        measurable_const measurable_const
    exact h_ind.mul
      ((M_mode.measurable_w s (α (L.unpaired a))).comp
        ((measurable_pi_apply a).comp measurable_fst))
  have h_joint : Measurable
      (fun pk : (L.InternalChord → Fin 3 → ℝ) × (Fin r → Fin 3 → ℝ) =>
        fockPartialIntWeight m C α L pk.1 * φ (L.partialMomentum m pk.1 pk.2)) :=
    ((measurable_fockPartialIntWeight hC α L).comp measurable_fst).mul
      (hφ.measurable_φ.comp (L.measurable_partialMomentum_uncurry m))
  have h_int : Measurable (fun k_ext : Fin r → Fin 3 → ℝ =>
      ∫ p_int : L.InternalChord → Fin 3 → ℝ,
        fockPartialIntWeight m C α L p_int * φ (L.partialMomentum m p_int k_ext)) :=
    (h_joint.stronglyMeasurable.integral_prod_left' (μ := volume)).measurable
  exact (measurable_const.mul h_w).mul (h_int.comp measurable_fst)

lemma memLp_fockPartialTerm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    {j r : ℕ} (α : Fin j → ι) {φ : (Fin j → Fin 4 → ℝ) → ℂ}
    (hφ : PartialMomentumBound m j φ) (L : PartialPairing j r) :
    MemLp (fockPartialTerm M_mode α φ L) 2 (fockSectorMeasure M_mode.ν r) := by
  have hm := measurable_fockPartialTerm M_mode hC α hφ L
  rw [memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable]
  rcases exists_norm_fockPartialIntWeight_le hC α L with ⟨B, hB_nn, hB⟩
  rcases hφ.bound r L with ⟨K, u, v, hK_nn, hu_int, _, hv_sq_int, hu_nn, hv_nn, hbound⟩
  let Iu : ℝ := ∫ p_int : L.InternalChord → Fin 3 → ℝ, ∏ c, u c (p_int c)
  have hIu_nn : 0 ≤ Iu :=
    integral_nonneg (fun p_int => Finset.prod_nonneg (fun c _ => hu_nn c (p_int c)))
  let CL : ℝ := M_mode.M ^ r * (B * K * Iu)
  have hCL_nn : 0 ≤ CL :=
    mul_nonneg (pow_nonneg M_mode.hM r) (mul_nonneg (mul_nonneg hB_nn hK_nn) hIu_nn)
  have h_pt : ∀ x : FockSectorDom M_mode.ν r,
      ‖fockPartialTerm M_mode α φ L x‖ ≤ CL * ∏ a : Fin r, v a (x.1 a) := by
    intro x
    unfold fockPartialTerm
    rw [norm_mul, norm_mul, norm_eta_pow M_mode.hη, one_mul, norm_prod]
    have hw_le : (∏ a : Fin r, ‖M_mode.w (x.2 a) (x.1 a) (α (L.unpaired a))‖) ≤ M_mode.M ^ r := by
      calc (∏ a : Fin r, ‖M_mode.w (x.2 a) (x.1 a) (α (L.unpaired a))‖)
          ≤ ∏ _a : Fin r, M_mode.M :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _)
              (fun a _ => M_mode.norm_w_le _ _ _)
        _ = M_mode.M ^ r := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hint_le :
        ‖∫ p_int : L.InternalChord → Fin 3 → ℝ,
          fockPartialIntWeight m C α L p_int * φ (L.partialMomentum m p_int x.1)‖ ≤
          (B * K * Iu) * ∏ a : Fin r, v a (x.1 a) := by
      have h_dom_int : Integrable (fun p_int : L.InternalChord → Fin 3 → ℝ =>
          (B * K * ∏ a : Fin r, v a (x.1 a)) * ∏ c, u c (p_int c)) volume :=
        (Integrable.fintype_prod (f := u) hu_int).const_mul _
      calc ‖∫ p_int : L.InternalChord → Fin 3 → ℝ,
            fockPartialIntWeight m C α L p_int * φ (L.partialMomentum m p_int x.1)‖
          ≤ ∫ p_int : L.InternalChord → Fin 3 → ℝ,
              ‖fockPartialIntWeight m C α L p_int * φ (L.partialMomentum m p_int x.1)‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ p_int : L.InternalChord → Fin 3 → ℝ,
              (B * K * ∏ a : Fin r, v a (x.1 a)) * ∏ c, u c (p_int c) := by
            refine integral_mono_of_nonneg
              (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) h_dom_int
              (Filter.Eventually.of_forall (fun p_int => ?_))
            dsimp only
            rw [norm_mul]
            calc ‖fockPartialIntWeight m C α L p_int‖ * ‖φ (L.partialMomentum m p_int x.1)‖
                ≤ B * (K * (∏ c, u c (p_int c)) * (∏ a, v a (x.1 a))) :=
                  mul_le_mul (hB p_int) (hbound p_int x.1) (norm_nonneg _) hB_nn
              _ = (B * K * ∏ a : Fin r, v a (x.1 a)) * ∏ c, u c (p_int c) := by ring
        _ = (B * K * ∏ a : Fin r, v a (x.1 a)) * Iu := integral_const_mul _ _
        _ = (B * K * Iu) * ∏ a : Fin r, v a (x.1 a) := by ring
    calc (∏ a : Fin r, ‖M_mode.w (x.2 a) (x.1 a) (α (L.unpaired a))‖) *
          ‖∫ p_int : L.InternalChord → Fin 3 → ℝ,
            fockPartialIntWeight m C α L p_int * φ (L.partialMomentum m p_int x.1)‖
        ≤ M_mode.M ^ r * ((B * K * Iu) * ∏ a : Fin r, v a (x.1 a)) :=
          mul_le_mul hw_le hint_le (norm_nonneg _) (pow_nonneg M_mode.hM r)
      _ = CL * ∏ a : Fin r, v a (x.1 a) := by dsimp [CL]; ring
  have h_dom_k : Integrable
      (fun k_ext : Fin r → Fin 3 → ℝ => CL ^ 2 * ∏ a : Fin r, (v a (k_ext a)) ^ 2) volume :=
    (Integrable.fintype_prod (f := fun a q => (v a q) ^ 2) hv_sq_int).const_mul (CL ^ 2)
  have h_dom : Integrable
      (fun x : FockSectorDom M_mode.ν r =>
        (CL ^ 2 * ∏ a : Fin r, (v a (x.1 a)) ^ 2) * (1 : ℝ))
      (fockSectorMeasure M_mode.ν r) :=
    h_dom_k.mul_prod (integrable_const (1 : ℝ))
  refine h_dom.mono' ((hm.norm).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => ?_))
  rw [Real.norm_of_nonneg (sq_nonneg _), mul_one, Finset.prod_pow, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h_pt x) 2

noncomputable def fockRawSector {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) {j : ℕ} (r : ℕ) (α : Fin j → ι)
    (φ : (Fin j → Fin 4 → ℝ) → ℂ) (x : FockSectorDom M_mode.ν r) : ℂ :=
  ∑ L : PartialPairing j r, fockPartialTerm M_mode α φ L x

lemma measurable_fockRawSector {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    {j : ℕ} (r : ℕ) (α : Fin j → ι) {φ : (Fin j → Fin 4 → ℝ) → ℂ}
    (hφ : PartialMomentumBound m j φ) :
    Measurable (fockRawSector M_mode r α φ) :=
  Finset.measurable_sum Finset.univ (fun L _ => measurable_fockPartialTerm M_mode hC α hφ L)

lemma memLp_fockRawSector {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    {j : ℕ} (r : ℕ) (α : Fin j → ι) {φ : (Fin j → Fin 4 → ℝ) → ℂ}
    (hφ : PartialMomentumBound m j φ) :
    MemLp (fockRawSector M_mode r α φ) 2 (fockSectorMeasure M_mode.ν r) :=
  memLp_finsetSum Finset.univ (fun L _ => memLp_fockPartialTerm M_mode hC α hφ L)

noncomputable def fockMomentumVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (j : ℕ) (α : Fin j → ι) (φ : (Fin j → Fin 4 → ℝ) → ℂ)
    (hφ : PartialMomentumBound m j φ) : FockHilbert M_mode.ν :=
  ∑ r ∈ Finset.range (j + 1),
    liftSectorToFock M_mode.ν r
      (symmSector M_mode.ν r η (fockRawSector M_mode r α φ))
      (measurable_symmSector η (measurable_fockRawSector M_mode hC r α hφ))
      (memLp_symmSector η (memLp_fockRawSector M_mode hC r α hφ))

lemma star_massShellWeight_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} (S : StarStructure R_rep) (m : ℝ)
    (C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (α₀ α₁ : ι) (q : Fin 3 → ℝ) :
    star (massShellWeight m C ![α₀, α₁] q) =
      ∑ γ : Fin 2 → ι, (S.C α₀ (γ 0) * S.C α₁ (γ 1)) *
        massShellWeight m C (γ ∘ Fin.rev) q := by
  unfold massShellWeight
  rw [Complex.star_def, map_mul, map_inv₀, map_mul, map_ofNat, Complex.conj_ofReal,
    ← Complex.star_def, hC_herm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  rw [Fin.prod_univ_two]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

lemma integrable_mul_of_sq {u v : (Fin 3 → ℝ) → ℝ}
    (hu_meas : AEStronglyMeasurable u volume) (hv_meas : AEStronglyMeasurable v volume)
    (hu_sq : Integrable (fun q => (u q) ^ 2) volume)
    (hv_sq : Integrable (fun q => (v q) ^ 2) volume) :
    Integrable (fun q : Fin 3 → ℝ => u q * v q) volume := by
  have h_dom : Integrable (fun q : Fin 3 → ℝ => ((u q) ^ 2 + (v q) ^ 2) / 2) volume :=
    (hu_sq.add hv_sq).div_const 2
  refine h_dom.mono' (hu_meas.mul hv_meas) (Filter.Eventually.of_forall (fun q => ?_))
  rw [Real.norm_eq_abs, abs_mul]
  have h_amgm : 2 * (|u q| * |v q|) ≤ |u q| ^ 2 + |v q| ^ 2 := by
    nlinarith [sq_nonneg (|u q| - |v q|)]
  rw [sq_abs, sq_abs] at h_amgm
  linarith

theorem inner_fockPartialTerm_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    {j k r : ℕ} (α : Fin j → ι) (α' : Fin k → ι)
    {φ₁ : (Fin j → Fin 4 → ℝ) → ℂ} {φ₂ : (Fin k → Fin 4 → ℝ) → ℂ}
    (hφ₁ : PartialMomentumBound m j φ₁) (hφ₂ : PartialMomentumBound m k φ₂)
    (L : PartialPairing j r) (R : PartialPairing k r) (σ : Equiv.Perm (Fin r)) :
    η ^ permInversions σ *
      (∫ x : FockSectorDom M_mode.ν r,
        star (fockPartialTerm M_mode α φ₁ L x) *
          fockPartialTerm M_mode α' φ₂ R (x.1 ∘ σ.symm, x.2 ∘ σ.symm)
        ∂(fockSectorMeasure M_mode.ν r)) =
    ∑ β : Fin j → ι, (∏ i : Fin j, S.C (α i) (β i)) *
      ((η ^ (PartialPairing.concatRev L R σ).cross) *
        ∫ p : (PartialPairing.concatRev L R σ).Chord → Fin 3 → ℝ,
          wickChordWeight m C (PartialPairing.concatRev L R σ) (Fin.append (β ∘ Fin.rev) α') p *
            (star (φ₁ (fun i =>
                -(PartialPairing.concatRev L R σ).momentum m p (Fin.castAdd k (Fin.rev i)))) *
              φ₂ (fun t =>
                (PartialPairing.concatRev L R σ).momentum m p (Fin.natAdd j t)))) := by
  let P := PartialPairing.concatRev L R σ
  have hm1 := memLp_fockPartialTerm M_mode hC α hφ₁ L
  have hm2 := (memLp_fockPartialTerm M_mode hC α' hφ₂ R).comp_measurePreserving
    (measurePreserving_fockSectorPermEquiv M_mode.ν r σ.symm)
  have h_x_int : Integrable
      (fun x : FockSectorDom M_mode.ν r =>
        star (fockPartialTerm M_mode α φ₁ L x) *
          fockPartialTerm M_mode α' φ₂ R (x.1 ∘ σ.symm, x.2 ∘ σ.symm))
      (fockSectorMeasure M_mode.ν r) := by
    have hi := L2.integrable_inner (𝕜 := ℂ) (hm1.toLp _) (hm2.toLp _)
    refine hi.congr ?_
    filter_upwards [hm1.coeFn_toLp, hm2.coeFn_toLp] with x hx1 hx2
    rw [RCLike.inner_apply, hx1, hx2]
    simp [mul_comm]
  unfold fockSectorMeasure at h_x_int ⊢
  rw [integral_prod _ h_x_int]
  simp_rw [integral_count]
  let IL : (Fin r → Fin 3 → ℝ) → ℂ := fun k_ext =>
    ∫ p_L : L.InternalChord → Fin 3 → ℝ,
      fockPartialIntWeight m C α L p_L * φ₁ (L.partialMomentum m p_L k_ext)
  let IR : (Fin r → Fin 3 → ℝ) → ℂ := fun k_ext =>
    ∫ p_R : R.InternalChord → Fin 3 → ℝ,
      fockPartialIntWeight m C α' R p_R * φ₂ (R.partialMomentum m p_R (k_ext ∘ σ.symm))
  have h_spin_sum : ∀ k_ext : Fin r → Fin 3 → ℝ,
      (∑ s : Fin r → Fin M_mode.ν,
        star (fockPartialTerm M_mode α φ₁ L (k_ext, s)) *
          fockPartialTerm M_mode α' φ₂ R (k_ext ∘ σ.symm, s ∘ σ.symm)) =
      (η ^ L.partialCross * η ^ R.partialCross) *
        (∏ a : Fin r,
          ∑ δ_a : ι, S.C (α (L.unpaired a)) δ_a *
            massShellWeight m C ![δ_a, α' (R.unpaired (σ a))] (k_ext a)) *
        (star (IL k_ext) * IR k_ext) := by
    intro k_ext
    have h_term : ∀ s : Fin r → Fin M_mode.ν,
        star (fockPartialTerm M_mode α φ₁ L (k_ext, s)) *
          fockPartialTerm M_mode α' φ₂ R (k_ext ∘ σ.symm, s ∘ σ.symm) =
        ((η ^ L.partialCross * η ^ R.partialCross) * (star (IL k_ext) * IR k_ext)) *
          ∏ a : Fin r,
            star (M_mode.w (s a) (k_ext a) (α (L.unpaired a))) *
              M_mode.w (s a) (k_ext a) (α' (R.unpaired (σ a))) := by
      intro s
      unfold fockPartialTerm
      change star (η ^ L.partialCross *
          (∏ a : Fin r, M_mode.w (s a) (k_ext a) (α (L.unpaired a))) * IL k_ext) *
        (η ^ R.partialCross *
          (∏ b : Fin r, M_mode.w (s (σ.symm b)) (k_ext (σ.symm b)) (α' (R.unpaired b))) *
          IR k_ext) = _
      have h_reidx :
          (∏ b : Fin r, M_mode.w (s (σ.symm b)) (k_ext (σ.symm b)) (α' (R.unpaired b))) =
          ∏ a : Fin r, M_mode.w (s a) (k_ext a) (α' (R.unpaired (σ a))) := by
        rw [← Equiv.prod_comp σ]
        simp
      rw [h_reidx, star_mul', star_mul', star_eta_pow M_mode.hη, star_prod]
      have h_pmul :
          (∏ a : Fin r, star (M_mode.w (s a) (k_ext a) (α (L.unpaired a)))) *
            (∏ a : Fin r, M_mode.w (s a) (k_ext a) (α' (R.unpaired (σ a)))) =
          ∏ a : Fin r,
            star (M_mode.w (s a) (k_ext a) (α (L.unpaired a))) *
              M_mode.w (s a) (k_ext a) (α' (R.unpaired (σ a))) :=
        Finset.prod_mul_distrib.symm
      calc η ^ L.partialCross *
            (∏ x : Fin r, star (M_mode.w (s x) (k_ext x) (α (L.unpaired x)))) *
            star (IL k_ext) *
            (η ^ R.partialCross *
              (∏ a : Fin r, M_mode.w (s a) (k_ext a) (α' (R.unpaired (σ a)))) * IR k_ext)
          = ((η ^ L.partialCross * η ^ R.partialCross) * (star (IL k_ext) * IR k_ext)) *
              ((∏ a : Fin r, star (M_mode.w (s a) (k_ext a) (α (L.unpaired a)))) *
                (∏ a : Fin r, M_mode.w (s a) (k_ext a) (α' (R.unpaired (σ a))))) := by ring
        _ = _ := by rw [h_pmul]
    simp_rw [h_term]
    have h_ps :
        (∑ s : Fin r → Fin M_mode.ν,
          ∏ a : Fin r,
            star (M_mode.w (s a) (k_ext a) (α (L.unpaired a))) *
              M_mode.w (s a) (k_ext a) (α' (R.unpaired (σ a)))) =
        ∏ a : Fin r, ∑ s_a : Fin M_mode.ν,
          star (M_mode.w s_a (k_ext a) (α (L.unpaired a))) *
            M_mode.w s_a (k_ext a) (α' (R.unpaired (σ a))) :=
      (Fintype.prod_sum (fun (a : Fin r) (s_a : Fin M_mode.ν) =>
        star (M_mode.w s_a (k_ext a) (α (L.unpaired a))) *
          M_mode.w s_a (k_ext a) (α' (R.unpaired (σ a))))).symm
    have h_fw :
        (∏ a : Fin r, ∑ s_a : Fin M_mode.ν,
          star (M_mode.w s_a (k_ext a) (α (L.unpaired a))) *
            M_mode.w s_a (k_ext a) (α' (R.unpaired (σ a)))) =
        ∏ a : Fin r, ∑ δ_a : ι, S.C (α (L.unpaired a)) δ_a *
          massShellWeight m C ![δ_a, α' (R.unpaired (σ a))] (k_ext a) :=
      Finset.prod_congr rfl (fun a _ => (M_mode.factor_weight _ _ _).symm)
    rw [← Finset.mul_sum, h_ps, h_fw]
    ring
  simp_rw [h_spin_sum]
  have h_joint_int : ∀ β : Fin j → ι,
      Integrable
        (fun q : ((L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ)) ×
            (Fin r → Fin 3 → ℝ) =>
          wickChordWeight m C P (Fin.append (β ∘ Fin.rev) α')
              (PartialPairing.concatRevParamEquiv L R σ q) *
            (star (φ₁ (L.partialMomentum m q.1.1 q.2)) *
              φ₂ (R.partialMomentum m q.1.2 (q.2 ∘ σ.symm)))) volume := by
    intro β
    rcases exists_norm_wickChordWeight_le hC P (Fin.append (β ∘ Fin.rev) α') with ⟨Bw, hBw_nn, hBw⟩
    rcases hφ₁.bound r L with ⟨K₁, u₁, v₁, hK₁_nn, hu₁_int, hv₁_meas, hv₁_sq, hu₁_nn, hv₁_nn, hb₁⟩
    rcases hφ₂.bound r R with ⟨K₂, u₂, v₂, hK₂_nn, hu₂_int, hv₂_meas, hv₂_sq, _, hv₂_nn, hb₂⟩
    let C0 : ℝ := Bw * K₁ * K₂
    have hC0_nn : 0 ≤ C0 := mul_nonneg (mul_nonneg hBw_nn hK₁_nn) hK₂_nn
    have h_dom_L : Integrable
        (fun p_L : L.InternalChord → Fin 3 → ℝ => C0 * ∏ cL, u₁ cL (p_L cL)) volume :=
      (Integrable.fintype_prod (f := u₁) hu₁_int).const_mul C0
    have h_dom_R : Integrable
        (fun p_R : R.InternalChord → Fin 3 → ℝ => ∏ cR, u₂ cR (p_R cR)) volume :=
      Integrable.fintype_prod (f := u₂) hu₂_int
    have h_dom_k : Integrable
        (fun k_ext : Fin r → Fin 3 → ℝ => ∏ a : Fin r, (v₁ a (k_ext a) * v₂ (σ a) (k_ext a)))
        volume := by
      refine Integrable.fintype_prod (f := fun a q => v₁ a q * v₂ (σ a) q) (fun a => ?_)
      exact integrable_mul_of_sq (hv₁_meas a).aestronglyMeasurable
        (hv₂_meas (σ a)).aestronglyMeasurable (hv₁_sq a) (hv₂_sq (σ a))
    have h_dom : Integrable
        (fun q : ((L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ)) ×
            (Fin r → Fin 3 → ℝ) =>
          ((C0 * ∏ cL, u₁ cL (q.1.1 cL)) * (∏ cR, u₂ cR (q.1.2 cR))) *
            (∏ a : Fin r, (v₁ a (q.2 a) * v₂ (σ a) (q.2 a)))) volume :=
      (h_dom_L.mul_prod h_dom_R).mul_prod h_dom_k
    have h_meas_w : Measurable
        (fun q : ((L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ)) ×
            (Fin r → Fin 3 → ℝ) =>
          wickChordWeight m C P (Fin.append (β ∘ Fin.rev) α')
            (PartialPairing.concatRevParamEquiv L R σ q)) :=
      (measurable_wickChordWeight hC P (Fin.append (β ∘ Fin.rev) α')).comp
        (PartialPairing.concatRevParamEquiv L R σ).measurable
    have h_meas_1 : Measurable
        (fun q : ((L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ)) ×
            (Fin r → Fin 3 → ℝ) =>
          star (φ₁ (L.partialMomentum m q.1.1 q.2))) :=
      continuous_star.measurable.comp <| hφ₁.measurable_φ.comp <|
        ((L.continuous_partialMomentum_uncurry m).comp
          ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).measurable
    have h_cont_kσ : Continuous
        (fun q : ((L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ)) ×
            (Fin r → Fin 3 → ℝ) => q.2 ∘ σ.symm) :=
      continuous_pi (fun b => (continuous_apply (σ.symm b)).comp continuous_snd)
    have h_meas_2 : Measurable
        (fun q : ((L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ)) ×
            (Fin r → Fin 3 → ℝ) =>
          φ₂ (R.partialMomentum m q.1.2 (q.2 ∘ σ.symm))) :=
      hφ₂.measurable_φ.comp <|
        ((R.continuous_partialMomentum_uncurry m).comp
          ((continuous_snd.comp continuous_fst).prodMk h_cont_kσ)).measurable
    refine h_dom.mono' (h_meas_w.mul (h_meas_1.mul h_meas_2)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun q => ?_))
    rw [norm_mul, norm_mul, norm_star]
    have hv_reidx : (∏ b : Fin r, v₂ b (q.2 (σ.symm b))) = ∏ a : Fin r, v₂ (σ a) (q.2 a) := by
      rw [← Equiv.prod_comp σ]
      simp
    have h1 := hb₁ q.1.1 q.2
    have h2 := hb₂ q.1.2 (q.2 ∘ σ.symm)
    dsimp only [Function.comp_apply] at h2
    rw [hv_reidx] at h2
    have h12 : ‖φ₁ (L.partialMomentum m q.1.1 q.2)‖ *
        ‖φ₂ (R.partialMomentum m q.1.2 (q.2 ∘ σ.symm))‖ ≤
        (K₁ * (∏ cL, u₁ cL (q.1.1 cL)) * (∏ a, v₁ a (q.2 a))) *
          (K₂ * (∏ cR, u₂ cR (q.1.2 cR)) * (∏ a, v₂ (σ a) (q.2 a))) :=
      mul_le_mul h1 h2 (norm_nonneg _) (by
        exact mul_nonneg (mul_nonneg hK₁_nn
          (Finset.prod_nonneg (fun c _ => hu₁_nn c (q.1.1 c))))
          (Finset.prod_nonneg (fun a _ => hv₁_nn a (q.2 a))))
    calc ‖wickChordWeight m C P (Fin.append (β ∘ Fin.rev) α')
            (PartialPairing.concatRevParamEquiv L R σ q)‖ *
          (‖φ₁ (L.partialMomentum m q.1.1 q.2)‖ *
            ‖φ₂ (R.partialMomentum m q.1.2 (q.2 ∘ σ.symm))‖)
        ≤ Bw * ((K₁ * (∏ cL, u₁ cL (q.1.1 cL)) * (∏ a, v₁ a (q.2 a))) *
            (K₂ * (∏ cR, u₂ cR (q.1.2 cR)) * (∏ a, v₂ (σ a) (q.2 a)))) :=
          mul_le_mul (hBw _) h12 (by positivity) hBw_nn
      _ = ((C0 * ∏ cL, u₁ cL (q.1.1 cL)) * (∏ cR, u₂ cR (q.1.2 cR))) *
            ((∏ a : Fin r, v₁ a (q.2 a)) * (∏ a : Fin r, v₂ (σ a) (q.2 a))) := by
          dsimp [C0]; ring
      _ = ((C0 * ∏ cL, u₁ cL (q.1.1 cL)) * (∏ cR, u₂ cR (q.1.2 cR))) *
            (∏ a : Fin r, (v₁ a (q.2 a) * v₂ (σ a) (q.2 a))) := by
          rw [Finset.prod_mul_distrib]
  have h_k_eq : ∀ k_ext : Fin r → Fin 3 → ℝ,
      (η ^ L.partialCross * η ^ R.partialCross) *
        (∏ a : Fin r,
          ∑ δ_a : ι, S.C (α (L.unpaired a)) δ_a *
            massShellWeight m C ![δ_a, α' (R.unpaired (σ a))] (k_ext a)) *
        (star (IL k_ext) * IR k_ext) =
      ∑ β : Fin j → ι, (∏ i : Fin j, S.C (α i) (β i)) *
        ((η ^ L.partialCross * η ^ R.partialCross) *
          ∫ pq : (L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ),
            wickChordWeight m C P (Fin.append (β ∘ Fin.rev) α')
                (PartialPairing.concatRevParamEquiv L R σ (pq, k_ext)) *
              (star (φ₁ (L.partialMomentum m pq.1 k_ext)) *
                φ₂ (R.partialMomentum m pq.2 (k_ext ∘ σ.symm)))) := by
    intro k_ext
    have hIL_star : star (IL k_ext) =
        ∫ p_L : L.InternalChord → Fin 3 → ℝ,
          star (fockPartialIntWeight m C α L p_L) *
            star (φ₁ (L.partialMomentum m p_L k_ext)) := by
      rw [show IL k_ext = _ from rfl, Complex.star_def, ← integral_conj]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun p_L => ?_))
      simp
    rw [hIL_star]
    dsimp only [IR]
    rw [← integral_mul_const]
    simp_rw [← integral_const_mul]
    have h_pLR_int : Integrable
        (fun pq : (L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ) =>
          (η ^ L.partialCross * η ^ R.partialCross) *
            (∏ a : Fin r,
              ∑ δ_a : ι, S.C (α (L.unpaired a)) δ_a *
                massShellWeight m C ![δ_a, α' (R.unpaired (σ a))] (k_ext a)) *
            ((star (fockPartialIntWeight m C α L pq.1) *
                star (φ₁ (L.partialMomentum m pq.1 k_ext))) *
              (fockPartialIntWeight m C α' R pq.2 *
                φ₂ (R.partialMomentum m pq.2 (k_ext ∘ σ.symm))))) volume := by
      have hi0 := integrable_fockPartialIntegrand hC α hφ₁ L k_ext
      have hi1 : Integrable (fun p_L : L.InternalChord → Fin 3 → ℝ =>
          star (fockPartialIntWeight m C α L p_L * φ₁ (L.partialMomentum m p_L k_ext))) volume :=
        hi0.mono hi0.1.star (Filter.Eventually.of_forall (fun _ => (norm_star _).le))
      have hi2 := integrable_fockPartialIntegrand hC α' hφ₂ R (k_ext ∘ σ.symm)
      have hp := (hi1.mul_prod hi2).const_mul
        ((η ^ L.partialCross * η ^ R.partialCross) *
          ∏ a : Fin r,
            ∑ δ_a : ι, S.C (α (L.unpaired a)) δ_a *
              massShellWeight m C ![δ_a, α' (R.unpaired (σ a))] (k_ext a))
      refine hp.congr (Filter.Eventually.of_forall (fun pq => ?_))
      simp [star_mul']
    have h_fub :
        (∫ p_L : L.InternalChord → Fin 3 → ℝ,
          ∫ p_R : R.InternalChord → Fin 3 → ℝ,
            (η ^ L.partialCross * η ^ R.partialCross) *
              (∏ a : Fin r,
                ∑ δ_a : ι, S.C (α (L.unpaired a)) δ_a *
                  massShellWeight m C ![δ_a, α' (R.unpaired (σ a))] (k_ext a)) *
              ((star (fockPartialIntWeight m C α L p_L) *
                  star (φ₁ (L.partialMomentum m p_L k_ext))) *
                (fockPartialIntWeight m C α' R p_R *
                  φ₂ (R.partialMomentum m p_R (k_ext ∘ σ.symm))))) =
        ∫ pq : (L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ),
          (η ^ L.partialCross * η ^ R.partialCross) *
            (∏ a : Fin r,
              ∑ δ_a : ι, S.C (α (L.unpaired a)) δ_a *
                massShellWeight m C ![δ_a, α' (R.unpaired (σ a))] (k_ext a)) *
            ((star (fockPartialIntWeight m C α L pq.1) *
                star (φ₁ (L.partialMomentum m pq.1 k_ext))) *
              (fockPartialIntWeight m C α' R pq.2 *
                φ₂ (R.partialMomentum m pq.2 (k_ext ∘ σ.symm)))) :=
      (integral_prod _ h_pLR_int).symm
    rw [h_fub]
    have h_alg_pq : ∀ pq : (L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ),
        (η ^ L.partialCross * η ^ R.partialCross) *
          (∏ a : Fin r,
            ∑ δ_a : ι, S.C (α (L.unpaired a)) δ_a *
              massShellWeight m C ![δ_a, α' (R.unpaired (σ a))] (k_ext a)) *
          ((star (fockPartialIntWeight m C α L pq.1) *
              star (φ₁ (L.partialMomentum m pq.1 k_ext))) *
            (fockPartialIntWeight m C α' R pq.2 *
              φ₂ (R.partialMomentum m pq.2 (k_ext ∘ σ.symm)))) =
        ∑ β : Fin j → ι, (∏ i : Fin j, S.C (α i) (β i)) *
          ((η ^ L.partialCross * η ^ R.partialCross) *
            (wickChordWeight m C P (Fin.append (β ∘ Fin.rev) α')
                (PartialPairing.concatRevParamEquiv L R σ (pq, k_ext)) *
              (star (φ₁ (L.partialMomentum m pq.1 k_ext)) *
                φ₂ (R.partialMomentum m pq.2 (k_ext ∘ σ.symm))))) := by
      intro ⟨p_L, p_R⟩
      have h_star_L : star (fockPartialIntWeight m C α L p_L) =
          ∏ cL : L.InternalChord,
            ∑ γ : Fin 2 → ι, (S.C (α cL.1) (γ 0) * S.C (α (L.mate cL.1)) (γ 1)) *
              massShellWeight m C (γ ∘ Fin.rev) (p_L cL) := by
        unfold fockPartialIntWeight
        rw [star_prod]
        refine Finset.prod_congr rfl (fun cL _ => ?_)
        exact star_massShellWeight_eq S m C hC_herm (α cL.1) (α (L.mate cL.1)) (p_L cL)
      have h_cross_sum :
          (∏ a : Fin r,
            ∑ δ_a : ι, S.C (α (L.unpaired a)) δ_a *
              massShellWeight m C ![δ_a, α' (R.unpaired (σ a))] (k_ext a)) =
          ∑ δ : Fin r → ι,
            (∏ a : Fin r, S.C (α (L.unpaired a)) (δ a)) *
              (∏ a : Fin r, massShellWeight m C ![δ a, α' (R.unpaired (σ a))] (k_ext a)) := by
        rw [Fintype.prod_sum]
        refine Finset.sum_congr rfl (fun δ _ => Finset.prod_mul_distrib)
      have h_factor := (L.sum_prod_partial_factor
        (fun i b => S.C (α i) b)
        (fun δ => ∏ a : Fin r, massShellWeight m C ![δ a, α' (R.unpaired (σ a))] (k_ext a))
        (fun cL γ => massShellWeight m C (γ ∘ Fin.rev) (p_L cL))).symm
      rw [h_star_L, h_cross_sum]
      calc (η ^ L.partialCross * η ^ R.partialCross) *
            (∑ δ : Fin r → ι,
              (∏ a : Fin r, S.C (α (L.unpaired a)) (δ a)) *
                ∏ a : Fin r, massShellWeight m C ![δ a, α' (R.unpaired (σ a))] (k_ext a)) *
            (((∏ cL : L.InternalChord,
                ∑ γ : Fin 2 → ι, (S.C (α cL.1) (γ 0) * S.C (α (L.mate cL.1)) (γ 1)) *
                  massShellWeight m C (γ ∘ Fin.rev) (p_L cL)) *
                star (φ₁ (L.partialMomentum m p_L k_ext))) *
              (fockPartialIntWeight m C α' R p_R *
                φ₂ (R.partialMomentum m p_R (k_ext ∘ σ.symm))))
          = ((∑ δ : Fin r → ι,
              (∏ a : Fin r, S.C (α (L.unpaired a)) (δ a)) *
                ∏ a : Fin r, massShellWeight m C ![δ a, α' (R.unpaired (σ a))] (k_ext a)) *
              (∏ cL : L.InternalChord,
                ∑ γ : Fin 2 → ι, (S.C (α cL.1) (γ 0) * S.C (α (L.mate cL.1)) (γ 1)) *
                  massShellWeight m C (γ ∘ Fin.rev) (p_L cL))) *
            ((η ^ L.partialCross * η ^ R.partialCross) *
              fockPartialIntWeight m C α' R p_R *
              (star (φ₁ (L.partialMomentum m p_L k_ext)) *
                φ₂ (R.partialMomentum m p_R (k_ext ∘ σ.symm)))) := by ring
        _ = (∑ β : Fin j → ι,
              (∏ i : Fin j, S.C (α i) (β i)) *
                (∏ a : Fin r,
                  massShellWeight m C ![β (L.unpaired a), α' (R.unpaired (σ a))] (k_ext a)) *
                (∏ cL : L.InternalChord,
                  massShellWeight m C (![β cL.1, β (L.mate cL.1)] ∘ Fin.rev) (p_L cL))) *
            ((η ^ L.partialCross * η ^ R.partialCross) *
              fockPartialIntWeight m C α' R p_R *
              (star (φ₁ (L.partialMomentum m p_L k_ext)) *
                φ₂ (R.partialMomentum m p_R (k_ext ∘ σ.symm)))) := by
            rw [h_factor]
        _ = _ := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl (fun β _ => ?_)
            dsimp only [P]
            rw [PartialPairing.wickChordWeight_concatRev]
            unfold fockPartialIntWeight
            ring
    have h_each_pq_int : ∀ β : Fin j → ι,
        Integrable
          (fun pq : (L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ) =>
            (∏ i : Fin j, S.C (α i) (β i)) *
              ((η ^ L.partialCross * η ^ R.partialCross) *
                (wickChordWeight m C P (Fin.append (β ∘ Fin.rev) α')
                    (PartialPairing.concatRevParamEquiv L R σ (pq, k_ext)) *
                  (star (φ₁ (L.partialMomentum m pq.1 k_ext)) *
                    φ₂ (R.partialMomentum m pq.2 (k_ext ∘ σ.symm)))))) volume := by
      intro β
      have hw_eq : ∀ pq : (L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ),
          wickChordWeight m C P (Fin.append (β ∘ Fin.rev) α')
              (PartialPairing.concatRevParamEquiv L R σ (pq, k_ext)) *
            (star (φ₁ (L.partialMomentum m pq.1 k_ext)) *
              φ₂ (R.partialMomentum m pq.2 (k_ext ∘ σ.symm))) =
          (∏ a : Fin r,
            massShellWeight m C ![β (L.unpaired a), α' (R.unpaired (σ a))] (k_ext a)) *
          (((∏ cL : L.InternalChord,
              massShellWeight m C (![β cL.1, β (L.mate cL.1)] ∘ Fin.rev) (pq.1 cL)) *
              star (φ₁ (L.partialMomentum m pq.1 k_ext))) *
            (fockPartialIntWeight m C α' R pq.2 *
              φ₂ (R.partialMomentum m pq.2 (k_ext ∘ σ.symm)))) := by
        intro pq
        dsimp only [P, fockPartialIntWeight]
        rw [PartialPairing.wickChordWeight_concatRev]
        ring
      simp_rw [hw_eq]
      have hL_rev : Integrable (fun p_L : L.InternalChord → Fin 3 → ℝ =>
          (∏ cL : L.InternalChord,
            massShellWeight m C (![β cL.1, β (L.mate cL.1)] ∘ Fin.rev) (p_L cL)) *
            star (φ₁ (L.partialMomentum m p_L k_ext))) volume := by
        rcases hφ₁.bound r L with ⟨K₁, u₁, v₁, hK₁_nn, hu₁_int, _, _, _, hv₁_nn, hb₁⟩
        let Bc : L.InternalChord → ℝ := fun cL =>
          Classical.choose (hC.2 (![β cL.1, β (L.mate cL.1)] ∘ Fin.rev))
        have hBc : ∀ cL : L.InternalChord, 0 ≤ Bc cL ∧ ∀ q : Fin 3 → ℝ,
            ‖massShellWeight m C (![β cL.1, β (L.mate cL.1)] ∘ Fin.rev) q‖ ≤ Bc cL :=
          fun cL => Classical.choose_spec (hC.2 (![β cL.1, β (L.mate cL.1)] ∘ Fin.rev))
        let CL' : ℝ := (∏ cL, Bc cL) * K₁ * (∏ a, v₁ a (k_ext a))
        have h_dom' : Integrable (fun p_L : L.InternalChord → Fin 3 → ℝ =>
            CL' * ∏ cL, u₁ cL (p_L cL)) volume :=
          (Integrable.fintype_prod (f := u₁) hu₁_int).const_mul CL'
        have h_m' : Measurable (fun p_L : L.InternalChord → Fin 3 → ℝ =>
            (∏ cL : L.InternalChord,
              massShellWeight m C (![β cL.1, β (L.mate cL.1)] ∘ Fin.rev) (p_L cL)) *
              star (φ₁ (L.partialMomentum m p_L k_ext))) :=
          (Finset.measurable_prod Finset.univ (fun cL _ =>
            (measurable_massShellWeight hC _).comp (measurable_pi_apply cL))).mul
            (continuous_star.measurable.comp (hφ₁.measurable_φ.comp
              ((L.continuous_partialMomentum_uncurry m |>.comp
                (continuous_id.prodMk continuous_const)).measurable)))
        refine h_dom'.mono' h_m'.aestronglyMeasurable (Filter.Eventually.of_forall (fun p_L => ?_))
        rw [norm_mul, norm_star, norm_prod]
        have hB_le : (∏ cL, ‖massShellWeight m C (![β cL.1, β (L.mate cL.1)] ∘ Fin.rev) (p_L cL)‖) ≤
            ∏ cL, Bc cL :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun cL _ => (hBc cL).2 (p_L cL))
        calc (∏ cL, ‖massShellWeight m C (![β cL.1, β (L.mate cL.1)] ∘ Fin.rev) (p_L cL)‖) *
              ‖φ₁ (L.partialMomentum m p_L k_ext)‖
            ≤ (∏ cL, Bc cL) * (K₁ * (∏ cL, u₁ cL (p_L cL)) * (∏ a, v₁ a (k_ext a))) :=
              mul_le_mul hB_le (hb₁ p_L k_ext) (norm_nonneg _)
                (Finset.prod_nonneg (fun cL _ => (hBc cL).1))
          _ = CL' * ∏ cL, u₁ cL (p_L cL) := by dsimp [CL']; ring
      have hR_int := integrable_fockPartialIntegrand hC α' hφ₂ R (k_ext ∘ σ.symm)
      exact (((hL_rev.mul_prod hR_int).const_mul _).const_mul _).const_mul _
    simp_rw [h_alg_pq]
    rw [integral_finsetSum Finset.univ (fun β _ => h_each_pq_int β)]
  simp_rw [h_k_eq]
  have h_k_int : ∀ β : Fin j → ι,
      Integrable (fun k_ext : Fin r → Fin 3 → ℝ =>
        (∏ i : Fin j, S.C (α i) (β i)) *
          ((η ^ L.partialCross * η ^ R.partialCross) *
            ∫ pq : (L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ),
              wickChordWeight m C P (Fin.append (β ∘ Fin.rev) α')
                  (PartialPairing.concatRevParamEquiv L R σ (pq, k_ext)) *
                (star (φ₁ (L.partialMomentum m pq.1 k_ext)) *
                  φ₂ (R.partialMomentum m pq.2 (k_ext ∘ σ.symm))))) volume :=
    fun β => ((h_joint_int β).integral_prod_right.const_mul _).const_mul _
  rw [integral_finsetSum Finset.univ (fun β _ => h_k_int β), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  rw [integral_const_mul, integral_const_mul, ← integral_prod_symm _ (h_joint_int β)]
  change η ^ permInversions σ * ((∏ i : Fin j, S.C (α i) (β i)) *
      ((η ^ L.partialCross * η ^ R.partialCross) *
        ∫ q : ((L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ)) ×
            (Fin r → Fin 3 → ℝ),
          wickChordWeight m C P (Fin.append (β ∘ Fin.rev) α')
              (PartialPairing.concatRevParamEquiv L R σ q) *
            (star (φ₁ (L.partialMomentum m q.1.1 q.2)) *
              φ₂ (R.partialMomentum m q.1.2 (q.2 ∘ σ.symm))))) = _
  have hp_cross : η ^ L.partialCross * η ^ R.partialCross * η ^ permInversions σ =
      η ^ P.cross := by
    dsimp [P]
    rw [PartialPairing.cross_concatRev, pow_add, pow_add]
  have h_cross_eq : ∀ J : ℂ,
      η ^ permInversions σ * ((∏ i : Fin j, S.C (α i) (β i)) *
        ((η ^ L.partialCross * η ^ R.partialCross) * J)) =
      (∏ i : Fin j, S.C (α i) (β i)) * (η ^ P.cross * J) := by
    intro J
    calc η ^ permInversions σ * ((∏ i : Fin j, S.C (α i) (β i)) *
          ((η ^ L.partialCross * η ^ R.partialCross) * J))
        = (∏ i : Fin j, S.C (α i) (β i)) *
            ((η ^ L.partialCross * η ^ R.partialCross * η ^ permInversions σ) * J) := by ring
      _ = (∏ i : Fin j, S.C (α i) (β i)) * (η ^ P.cross * J) := by rw [hp_cross]
  rw [h_cross_eq]
  congr 2
  have h_mp := PartialPairing.measurePreserving_concatRevParamEquiv L R σ
  have h_push := h_mp.integral_comp (PartialPairing.concatRevParamEquiv L R σ).measurableEmbedding
    (fun p : P.Chord → Fin 3 → ℝ =>
      wickChordWeight m C P (Fin.append (β ∘ Fin.rev) α') p *
        (star (φ₁ (fun i => -P.momentum m p (Fin.castAdd k (Fin.rev i)))) *
          φ₂ (fun t => P.momentum m p (Fin.natAdd j t))))
  rw [← h_push]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun q => ?_))
  dsimp only [P]
  rcases q with ⟨⟨p_L, p_R⟩, k_ext⟩
  rw [PartialPairing.concatRev_momentum_left, PartialPairing.concatRev_momentum_right]

theorem inner_fockMomentumVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (j k : ℕ) (α : Fin j → ι) (α' : Fin k → ι)
    {φ₁ : (Fin j → Fin 4 → ℝ) → ℂ} {φ₂ : (Fin k → Fin 4 → ℝ) → ℂ}
    (hφ₁ : PartialMomentumBound m j φ₁) (hφ₂ : PartialMomentumBound m k φ₂) :
    ⟪fockMomentumVec M_mode hC j α φ₁ hφ₁, fockMomentumVec M_mode hC k α' φ₂ hφ₂⟫_ℂ =
      ∑ β : Fin j → ι, (∏ i : Fin j, S.C (α i) (β i)) *
        ∑ P : ChordPairing (j + k), η ^ P.cross *
          ∫ p : P.Chord → Fin 3 → ℝ,
            wickChordWeight m C P (Fin.append (β ∘ Fin.rev) α') p *
              (star (φ₁ (fun i => -P.momentum m p (Fin.castAdd k (Fin.rev i)))) *
                φ₂ (fun t => P.momentum m p (Fin.natAdd j t))) := by
  unfold fockMomentumVec
  rw [sum_inner]
  have h_diag : ∀ r₁ ∈ Finset.range (j + 1),
      ⟪liftSectorToFock M_mode.ν r₁
          (symmSector M_mode.ν r₁ η (fockRawSector M_mode r₁ α φ₁))
          (measurable_symmSector η (measurable_fockRawSector M_mode hC r₁ α hφ₁))
          (memLp_symmSector η (memLp_fockRawSector M_mode hC r₁ α hφ₁)),
        ∑ r₂ ∈ Finset.range (k + 1),
          liftSectorToFock M_mode.ν r₂
            (symmSector M_mode.ν r₂ η (fockRawSector M_mode r₂ α' φ₂))
            (measurable_symmSector η (measurable_fockRawSector M_mode hC r₂ α' hφ₂))
            (memLp_symmSector η (memLp_fockRawSector M_mode hC r₂ α' hφ₂))⟫_ℂ =
      if r₁ < k + 1 then
        ∫ x : FockSectorDom M_mode.ν r₁,
          star (symmSector M_mode.ν r₁ η (fockRawSector M_mode r₁ α φ₁) x) *
            symmSector M_mode.ν r₁ η (fockRawSector M_mode r₁ α' φ₂) x
          ∂(fockSectorMeasure M_mode.ν r₁)
      else 0 := by
    intro r₁ _
    rw [inner_sum]
    by_cases hr₁ : r₁ < k + 1
    · rw [if_pos hr₁, Finset.sum_eq_single r₁]
      · exact inner_liftSectorToFock_eq _ _ _ _
      · intro r₂ _ hne
        exact inner_liftSectorToFock_ne hne.symm _ _ _ _
      · intro hnot
        exact False.elim (hnot (Finset.mem_range.mpr hr₁))
    · rw [if_neg hr₁]
      refine Finset.sum_eq_zero (fun r₂ hr₂ => ?_)
      have hne : r₁ ≠ r₂ := by
        have hr₂_lt : r₂ < k + 1 := Finset.mem_range.mp hr₂
        omega
      exact inner_liftSectorToFock_ne hne _ _ _ _
  rw [Finset.sum_congr rfl h_diag, ← Finset.sum_filter]
  have h_filter_eq : (Finset.range (j + 1)).filter (· < k + 1) = Finset.range (min j k + 1) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [h_filter_eq, ← Fin.sum_univ_eq_sum_range]
  have h_sec : ∀ r : Fin (min j k + 1),
      (∫ x : FockSectorDom M_mode.ν r.val,
        star (symmSector M_mode.ν r.val η (fockRawSector M_mode r.val α φ₁) x) *
          symmSector M_mode.ν r.val η (fockRawSector M_mode r.val α' φ₂) x
        ∂(fockSectorMeasure M_mode.ν r.val)) =
      ∑ L : PartialPairing j r.val, ∑ R : PartialPairing k r.val, ∑ σ : Equiv.Perm (Fin r.val),
        ∑ β : Fin j → ι, (∏ i : Fin j, S.C (α i) (β i)) *
          ((η ^ (PartialPairing.concatRev L R σ).cross) *
            ∫ p : (PartialPairing.concatRev L R σ).Chord → Fin 3 → ℝ,
              wickChordWeight m C (PartialPairing.concatRev L R σ)
                  (Fin.append (β ∘ Fin.rev) α') p *
                (star (φ₁ (fun i =>
                    -(PartialPairing.concatRev L R σ).momentum m p
                      (Fin.castAdd k (Fin.rev i)))) *
                  φ₂ (fun t =>
                    (PartialPairing.concatRev L R σ).momentum m p (Fin.natAdd j t)))) := by
    intro r
    rw [inner_symmSector_eq M_mode.hη
      (memLp_fockRawSector M_mode hC r.val α hφ₁)
      (memLp_fockRawSector M_mode hC r.val α' hφ₂)]
    have h_pair_int : ∀ (σ : Equiv.Perm (Fin r.val))
        (L : PartialPairing j r.val) (R : PartialPairing k r.val),
        Integrable
          (fun x : FockSectorDom M_mode.ν r.val =>
            star (fockPartialTerm M_mode α φ₁ L x) *
              fockPartialTerm M_mode α' φ₂ R (x.1 ∘ σ.symm, x.2 ∘ σ.symm))
          (fockSectorMeasure M_mode.ν r.val) := by
      intro σ L R
      have hm1 := memLp_fockPartialTerm M_mode hC α hφ₁ L
      have hm2 := (memLp_fockPartialTerm M_mode hC α' hφ₂ R).comp_measurePreserving
        (measurePreserving_fockSectorPermEquiv M_mode.ν r.val σ.symm)
      have hi := L2.integrable_inner (𝕜 := ℂ) (hm1.toLp _) (hm2.toLp _)
      refine hi.congr ?_
      filter_upwards [hm1.coeFn_toLp, hm2.coeFn_toLp] with x hx1 hx2
      rw [RCLike.inner_apply, hx1, hx2]
      simp [mul_comm]
    have h_expand_raw : ∀ σ : Equiv.Perm (Fin r.val),
        η ^ permInversions σ *
          (∫ x : FockSectorDom M_mode.ν r.val,
            star (fockRawSector M_mode r.val α φ₁ x) *
              fockRawSector M_mode r.val α' φ₂ (x.1 ∘ σ.symm, x.2 ∘ σ.symm)
            ∂(fockSectorMeasure M_mode.ν r.val)) =
        ∑ L : PartialPairing j r.val, ∑ R : PartialPairing k r.val,
          η ^ permInversions σ *
            (∫ x : FockSectorDom M_mode.ν r.val,
              star (fockPartialTerm M_mode α φ₁ L x) *
                fockPartialTerm M_mode α' φ₂ R (x.1 ∘ σ.symm, x.2 ∘ σ.symm)
              ∂(fockSectorMeasure M_mode.ν r.val)) := by
      intro σ
      have h_fn :
          (fun x : FockSectorDom M_mode.ν r.val =>
            star (fockRawSector M_mode r.val α φ₁ x) *
              fockRawSector M_mode r.val α' φ₂ (x.1 ∘ σ.symm, x.2 ∘ σ.symm)) =
          fun x => ∑ L : PartialPairing j r.val, ∑ R : PartialPairing k r.val,
            star (fockPartialTerm M_mode α φ₁ L x) *
              fockPartialTerm M_mode α' φ₂ R (x.1 ∘ σ.symm, x.2 ∘ σ.symm) := by
        ext x
        unfold fockRawSector
        rw [star_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun L _ => Finset.mul_sum _ _ _)
      rw [h_fn, integral_finsetSum Finset.univ (fun L _ =>
        integrable_finsetSum Finset.univ (fun R _ => h_pair_int σ L R))]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun L _ => ?_)
      rw [integral_finsetSum Finset.univ (fun R _ => h_pair_int σ L R), Finset.mul_sum]
    simp_rw [h_expand_raw]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun L _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun R _ => ?_)
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    exact inner_fockPartialTerm_eq M_mode hC hC_herm α α' hφ₁ hφ₂ L R σ
  simp_rw [h_sec]
  have h_rhs_swap :
      (∑ β : Fin j → ι, (∏ i : Fin j, S.C (α i) (β i)) *
        ∑ P : ChordPairing (j + k), η ^ P.cross *
          ∫ p : P.Chord → Fin 3 → ℝ,
            wickChordWeight m C P (Fin.append (β ∘ Fin.rev) α') p *
              (star (φ₁ (fun i => -P.momentum m p (Fin.castAdd k (Fin.rev i)))) *
                φ₂ (fun t => P.momentum m p (Fin.natAdd j t)))) =
      ∑ r : Fin (min j k + 1), ∑ L : PartialPairing j r.val,
        ∑ R : PartialPairing k r.val, ∑ σ : Equiv.Perm (Fin r.val),
          ∑ β : Fin j → ι, (∏ i : Fin j, S.C (α i) (β i)) *
            ((η ^ (PartialPairing.concatRev L R σ).cross) *
              ∫ p : (PartialPairing.concatRev L R σ).Chord → Fin 3 → ℝ,
                wickChordWeight m C (PartialPairing.concatRev L R σ)
                    (Fin.append (β ∘ Fin.rev) α') p *
                  (star (φ₁ (fun i =>
                      -(PartialPairing.concatRev L R σ).momentum m p
                        (Fin.castAdd k (Fin.rev i)))) *
                    φ₂ (fun t =>
                      (PartialPairing.concatRev L R σ).momentum m p (Fin.natAdd j t)))) := by
    have h_equiv : ∀ β : Fin j → ι,
        (∑ P : ChordPairing (j + k), η ^ P.cross *
          ∫ p : P.Chord → Fin 3 → ℝ,
            wickChordWeight m C P (Fin.append (β ∘ Fin.rev) α') p *
              (star (φ₁ (fun i => -P.momentum m p (Fin.castAdd k (Fin.rev i)))) *
                φ₂ (fun t => P.momentum m p (Fin.natAdd j t)))) =
        ∑ r : Fin (min j k + 1), ∑ L : PartialPairing j r.val,
          ∑ R : PartialPairing k r.val, ∑ σ : Equiv.Perm (Fin r.val),
            (η ^ (PartialPairing.concatRev L R σ).cross) *
              ∫ p : (PartialPairing.concatRev L R σ).Chord → Fin 3 → ℝ,
                wickChordWeight m C (PartialPairing.concatRev L R σ)
                    (Fin.append (β ∘ Fin.rev) α') p *
                  (star (φ₁ (fun i =>
                      -(PartialPairing.concatRev L R σ).momentum m p
                        (Fin.castAdd k (Fin.rev i)))) *
                    φ₂ (fun t =>
                      (PartialPairing.concatRev L R σ).momentum m p (Fin.natAdd j t))) := by
      intro β
      rw [← (PartialPairing.chordPairingConcatRevEquiv j k).sum_comp, Fintype.sum_sigma]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun L _ => ?_)
      rw [Fintype.sum_prod_type]
      rfl
    simp_rw [h_equiv, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun L _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun R _ => ?_)
    rw [Finset.sum_comm]
  rw [h_rhs_swap]

lemma measurable_massShellDecay :
    Measurable (fun q : Fin 3 → ℝ => ((1 + ‖q‖) ^ 4)⁻¹) := by
  have hc : Continuous (fun q : Fin 3 → ℝ => (1 + ‖q‖) ^ 4) :=
    (continuous_const.add continuous_norm).pow 4
  exact (hc.inv₀ (fun q => ne_of_gt (pow_pos (by linarith [norm_nonneg q]) 4))).measurable

lemma integrable_sq_massShellDecay :
    Integrable (fun q : Fin 3 → ℝ => (((1 + ‖q‖) ^ 4)⁻¹) ^ 2) volume := by
  refine integrable_massShellDecay.mono' ?_ (Filter.Eventually.of_forall (fun q => ?_))
  · exact (measurable_massShellDecay.pow_const 2).aestronglyMeasurable
  · have h1 : 1 ≤ (1 + ‖q‖) ^ 4 := one_le_pow₀ (by linarith [norm_nonneg q])
    have h_inv_le : ((1 + ‖q‖) ^ 4)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    have h_nn : 0 ≤ ((1 + ‖q‖) ^ 4)⁻¹ := by positivity
    rw [Real.norm_of_nonneg (sq_nonneg _), sq]
    exact mul_le_of_le_one_right h_nn h_inv_le

lemma partialMomentumBound_minkowskiFourier (m : ℝ) (j : ℕ)
    (f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ) :
    PartialMomentumBound m j (minkowskiFourier f) := by
  have h_eq : minkowskiFourier f =
      fun q => (minkowskiFourierSchwartzCLM j f) (momentumToEuclidCLMN j q) := by
    ext q
    exact minkowskiFourier_eq_minkowskiFourierSchwartzCLM j f q
  refine ⟨?_, fun r L => ?_⟩
  · rw [h_eq]
    exact ((minkowskiFourierSchwartzCLM j f).continuous.comp
      (momentumToEuclidCLMN j).continuous).measurable
  · let g := minkowskiFourierSchwartzCLM j f
    let d := Fintype.card L.InternalChord + r
    let K : ℝ := (4 * Real.pi) ^ (4 * d) *
      ((Finset.Iic (4 * d, 0)).sup
        (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin j × Fin 4)) ℂ) g)
    have hK_nn : 0 ≤ K :=
      mul_nonneg (by positivity) (apply_nonneg _ g)
    refine ⟨K, fun _ q => ((1 + ‖q‖) ^ 4)⁻¹, fun _ q => ((1 + ‖q‖) ^ 4)⁻¹,
      hK_nn, fun _ => integrable_massShellDecay, fun _ => measurable_massShellDecay,
      fun _ => integrable_sq_massShellDecay,
      fun _ _ => by positivity, fun _ _ => by positivity, fun p_int k_ext => ?_⟩
    rw [h_eq]
    exact L.norm_schwartz_momentumToEuclid_partial_le m g p_int k_ext

noncomputable def fockSchwartzVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (j : ℕ) (α : Fin j → ι) (f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ) :
    FockHilbert M_mode.ν :=
  fockMomentumVec M_mode hC j α (minkowskiFourier f) (partialMomentumBound_minkowskiFourier m j f)

theorem inner_fockSchwartzVec_eq_wickMassShellW {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (j k : ℕ) (α : Fin j → ι) (α' : Fin k → ι)
    (f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (g : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ)
    (G : SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ)
    (hG : ∀ x : Fin (j + k) → Fin 4 → ℝ,
      G x = (starRingEnd ℂ) (f (fun i => x (Fin.castAdd k (Fin.rev i)))) *
        g (fun t => x (Fin.natAdd j t))) :
    ⟪fockSchwartzVec M_mode hC j α f, fockSchwartzVec M_mode hC k α' g⟫_ℂ =
      ∑ β : Fin j → ι, (∏ i : Fin j, S.C (α i) (β i)) *
        wickMassShellW m η C hC (j + k) (Fin.append (β ∘ Fin.rev) α') G := by
  unfold fockSchwartzVec
  rw [inner_fockMomentumVec M_mode hC hC_herm j k α α']
  refine Finset.sum_congr rfl (fun β _ => congrArg (_ * ·) ?_)
  rw [wickMassShellW_apply]
  refine Finset.sum_congr rfl (fun P _ => congrArg (_ * ·) ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  dsimp only
  rw [minkowskiFourier_borchersProduct_eq j k f g G hG (P.momentum m p)]

noncomputable def fockWightmanMap {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (A : WightmanConfig ι) : FockHilbert M_mode.ν :=
  fockSchwartzVec M_mode hC A.1 A.2.1 A.2.2.val

theorem inner_fockWightmanMap_eq_wightmanKernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (A B : WightmanConfig ι) :
    ⟪fockWightmanMap M_mode hC A, fockWightmanMap M_mode hC B⟫_ℂ =
      wightmanKernel S (wickMassShellW m η C hC) A B := by
  rcases A with ⟨j, α, f⟩
  rcases B with ⟨k, α', g⟩
  unfold fockWightmanMap wightmanKernel osConcatIdx
  exact inner_fockSchwartzVec_eq_wickMassShellW M_mode hC hC_herm j k α α'
    f.val g.val (wightmanConcatSchwartz j k f g) (wightmanConcatSchwartz_apply j k f g)

theorem wickMassShellPositivity {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q) :
    Positivity S (wickMassShellW m η C hC) :=
  positivity_of_hilbertWavepacketConfig S (wickMassShellW m η C hC)
    (fockWightmanMap M_mode hC)
    (inner_fockWightmanMap_eq_wightmanKernel M_mode hC hC_herm)

noncomputable def euclidLaplace {n : ℕ} (x : Fin n → Fin 4 → ℝ) (q : Fin n → Fin 4 → ℝ) : ℂ :=
  Complex.exp (∑ i : Fin n,
    ((q i 0 : ℂ) * (x i 0 : ℂ) +
      Complex.I * ((q i 1 : ℂ) * (x i 1 : ℂ) +
        (q i 2 : ℂ) * (x i 2 : ℂ) + (q i 3 : ℂ) * (x i 3 : ℂ))))

lemma continuous_euclidLaplace {n : ℕ} (x : Fin n → Fin 4 → ℝ) :
    Continuous (euclidLaplace x) := by
  unfold euclidLaplace
  refine Complex.continuous_exp.comp (continuous_finsetSum Finset.univ (fun i _ => ?_))
  have hc : ∀ μ : Fin 4, Continuous (fun q : Fin n → Fin 4 → ℝ => (q i μ : ℂ)) :=
    fun μ => Complex.continuous_ofReal.comp ((continuous_apply μ).comp (continuous_apply i))
  exact ((hc 0).mul continuous_const).add
    (continuous_const.mul
      ((((hc 1).mul continuous_const).add ((hc 2).mul continuous_const)).add
        ((hc 3).mul continuous_const)))

lemma vladimirov_kernel_osConcatPoint_eq (j k : ℕ)
    (x : Fin j → Fin 4 → ℝ) (y : Fin k → Fin 4 → ℝ) (p : Fin (j + k) → Fin 4 → ℝ) :
    vladimirov_kernel (j + k) (wickEmbedN (j + k) (osConcatPoint j k x y)) p =
      star (euclidLaplace x (fun i => -p (Fin.castAdd k (Fin.rev i)))) *
        euclidLaplace y (fun t => p (Fin.natAdd j t)) := by
  unfold vladimirov_kernel euclidLaplace
  rw [← (concatSlotEquiv j k).sum_comp, Fintype.sum_sum_type, mul_add,
    Complex.exp_add, Complex.star_def, ← Complex.exp_conj]
  congr 1
  · congr 1
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h_pt : wickEmbedN (j + k) (osConcatPoint j k x y)
        (concatSlotEquiv j k (Sum.inl i)) =
        wickEmbed (euclidTimeReflect (x i)) := by
      change wickEmbed (osConcatPoint j k x y (Fin.castAdd k (Fin.rev i))) = _
      rw [osConcatPoint_castAdd, Fin.rev_rev]
    rw [h_pt]
    change -Complex.I * minkowskiInnerC
        (fun μ => (p (Fin.castAdd k (Fin.rev i)) μ : ℂ))
        (wickEmbed (euclidTimeReflect (x i))) =
      (starRingEnd ℂ)
        (((-p (Fin.castAdd k (Fin.rev i)) 0 : ℝ) : ℂ) * (x i 0 : ℂ) +
          Complex.I *
            (((-p (Fin.castAdd k (Fin.rev i)) 1 : ℝ) : ℂ) * (x i 1 : ℂ) +
              ((-p (Fin.castAdd k (Fin.rev i)) 2 : ℝ) : ℂ) * (x i 2 : ℂ) +
              ((-p (Fin.castAdd k (Fin.rev i)) 3 : ℝ) : ℂ) * (x i 3 : ℂ)))
    simp only [minkowskiInnerC, wickEmbed, euclidTimeReflect, Fin.isValue, ↓reduceIte,
      Fin.reduceEq, map_add, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I,
      Complex.ofReal_neg]
    ring_nf
    simp only [Complex.I_sq]
    ring
  · congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    have h_pt : wickEmbedN (j + k) (osConcatPoint j k x y)
        (concatSlotEquiv j k (Sum.inr t)) = wickEmbed (y t) := by
      change wickEmbed (osConcatPoint j k x y (Fin.natAdd j t)) = _
      rw [osConcatPoint_natAdd]
    rw [h_pt]
    change -Complex.I * minkowskiInnerC
        (fun μ => (p (Fin.natAdd j t) μ : ℂ)) (wickEmbed (y t)) = _
    simp only [minkowskiInnerC, wickEmbed, Fin.isValue, ↓reduceIte, Fin.reduceEq]
    ring_nf
    simp only [Complex.I_sq]
    ring

lemma orderedEuclidN_time_lt_of_lt {n : ℕ} {x : Fin n → Fin 4 → ℝ}
    (hx : x ∈ orderedEuclidN n) {u v : Fin n} (huv : u < v) :
    x u 0 < x v 0 := by
  have h2 : ![wickEmbed (x u), wickEmbed (x v)] ∈ forward_tube_n 2 :=
    pair_mem_forward_tube_two (wickEmbedN_mem_forward_tube_n n hx) huv
  have h_ord : ![x u, x v] ∈ orderedEuclidN 2 := by
    rw [← wickEmbedN_mem_forward_tube_n_iff 2 ![x u, x v]]
    convert h2 using 1
    ext s μ
    fin_cases s <;> rfl
  exact h_ord 0 (by decide)

lemma norm_euclidLaplace_partialMomentum {j r : ℕ} (m : ℝ)
    (x : Fin j → Fin 4 → ℝ) (L : PartialPairing j r)
    (p_int : L.InternalChord → Fin 3 → ℝ) (k_ext : Fin r → Fin 3 → ℝ) :
    ‖euclidLaplace x (L.partialMomentum m p_int k_ext)‖ =
      (∏ c : L.InternalChord,
        Real.exp (-((x (L.mate c.1) 0 - x c.1 0) * massShellEnergy m (p_int c)))) *
      (∏ a : Fin r,
        Real.exp (-(x (L.unpaired a) 0 * massShellEnergy m (k_ext a)))) := by
  unfold euclidLaplace
  rw [Complex.norm_exp]
  have h_re_term : ∀ i : Fin j,
      (((L.partialMomentum m p_int k_ext i 0 : ℂ) * (x i 0 : ℂ) +
        Complex.I * ((L.partialMomentum m p_int k_ext i 1 : ℂ) * (x i 1 : ℂ) +
          (L.partialMomentum m p_int k_ext i 2 : ℂ) * (x i 2 : ℂ) +
          (L.partialMomentum m p_int k_ext i 3 : ℂ) * (x i 3 : ℂ)))).re =
      L.partialMomentum m p_int k_ext i 0 * x i 0 := by
    intro i
    simp [Complex.add_re, Complex.mul_re]
  rw [Complex.re_sum]
  simp_rw [h_re_term]
  have h_split :
      (∑ i : Fin j, L.partialMomentum m p_int k_ext i 0 * x i 0) =
      (∑ a : Fin r, -(x (L.unpaired a) 0 * massShellEnergy m (k_ext a))) +
      (∑ c : L.InternalChord, -((x (L.mate c.1) 0 - x c.1 0) * massShellEnergy m (p_int c))) := by
    rw [← L.partialSlotEquiv.sum_comp, Fintype.sum_sum_type, Fintype.sum_prod_type]
    congr 1
    · refine Finset.sum_congr rfl (fun a _ => ?_)
      have hs : L.partialSlotEquiv (Sum.inl a) = L.unpaired a := rfl
      rw [hs, L.partialMomentum_unpaired]
      simp [massShellVec]
      ring
    · refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Fin.sum_univ_two]
      have hs0 : L.partialSlotEquiv (Sum.inr (c, 0)) = c.1 := rfl
      have hs1 : L.partialSlotEquiv (Sum.inr (c, 1)) = L.mate c.1 := rfl
      rw [hs0, hs1, L.partialMomentum_fst, L.partialMomentum_mate]
      simp [massShellVec]
      ring
  rw [h_split, Real.exp_add, Real.exp_sum, Real.exp_sum, mul_comm]

lemma partialMomentumBound_euclidLaplace {m : ℝ} (hm : 0 < m) {j : ℕ}
    {x : Fin j → Fin 4 → ℝ} (hx : x ∈ posOrderedEuclidN j) :
    PartialMomentumBound m j (euclidLaplace x) := by
  refine ⟨(continuous_euclidLaplace x).measurable, fun r L => ?_⟩
  refine ⟨1,
    fun c q => Real.exp (-((x (L.mate c.1) 0 - x c.1 0) * massShellEnergy m q)),
    fun a q => Real.exp (-(x (L.unpaired a) 0 * massShellEnergy m q)),
    zero_le_one,
    fun c => integrable_exp_neg_massShellEnergy hm
      (sub_pos.mpr (orderedEuclidN_time_lt_of_lt hx.2 c.2)),
    fun a => (Real.continuous_exp.comp
      ((continuous_const.mul (continuous_massShellEnergy m)).neg)).measurable,
    fun a => ?_,
    fun _ _ => (Real.exp_pos _).le,
    fun _ _ => (Real.exp_pos _).le,
    fun p_int k_ext => ?_⟩
  · have h_sq : (fun q : Fin 3 → ℝ =>
        (Real.exp (-(x (L.unpaired a) 0 * massShellEnergy m q))) ^ 2) =
        fun q => Real.exp (-((2 * x (L.unpaired a) 0) * massShellEnergy m q)) := by
      ext q
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [h_sq]
    exact integrable_exp_neg_massShellEnergy hm (mul_pos two_pos (hx.1 (L.unpaired a)))
  · rw [one_mul, norm_euclidLaplace_partialMomentum]

noncomputable def fockOSMap {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (A : OSConfig ι) : FockHilbert M_mode.ν :=
  fockMomentumVec M_mode hC A.1 A.2.1 (euclidLaplace A.2.2.val)
    (partialMomentumBound_euclidLaplace hm A.2.2.property)

theorem inner_fockOSMap_eq_osKernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (A B : OSConfig ι) :
    ⟪fockOSMap hm M_mode hC A, fockOSMap hm M_mode hC B⟫_ℂ =
      osKernel S (wickMassShellS m hm η C hC) A B := by
  rcases A with ⟨j, α, x, hx⟩
  rcases B with ⟨k, α', y, hy⟩
  unfold fockOSMap osKernel osConcatIdx
  dsimp only
  rw [inner_fockMomentumVec M_mode hC hC_herm j k α α']
  refine Finset.sum_congr rfl (fun β _ => congrArg (_ * ·) ?_)
  change (∑ P : ChordPairing (j + k), η ^ P.cross * _) =
    wickMassShellH m η C (j + k) (Fin.append (β ∘ Fin.rev) α')
      (wickEmbedN (j + k) (osConcatPoint j k x y))
  rw [wickMassShellH_eq_sum_integral]
  refine Finset.sum_congr rfl (fun P _ => congrArg (_ * ·) ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  dsimp only
  rw [vladimirov_kernel_osConcatPoint_eq j k x y (P.momentum m p)]

theorem wickMassShellOSReflectionPositive {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q) :
    OSReflectionPositive S (wickMassShellS m hm η C hC) := by
  intro Ψ
  let v : FockHilbert M_mode.ν := Ψ.sum (fun A c => c • fockOSMap hm M_mode hC A)
  have h_inner : ⟪v, v⟫_ℂ = osPreInner S (wickMassShellS m hm η C hC) Ψ Ψ := by
    dsimp [v]
    unfold osPreInner
    simp only [Finsupp.sum]
    rw [sum_inner (𝕜 := ℂ)]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    rw [inner_smul_left, inner_sum (𝕜 := ℂ), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun B _ => ?_)
    rw [inner_smul_right, inner_fockOSMap_eq_osKernel hm M_mode hC hC_herm A B,
      ← Complex.star_def]
    ring
  rw [← h_inner]
  exact inner_self_nonneg (𝕜 := ℂ)

theorem wickMassShellOSAxioms {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R_rep : HolomorphicLorentzRep ι) (S : StarStructure R_rep)
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R_rep.rep A (α i) (β i)) * C β q)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R_rep.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q) :
    OSAxioms R_rep S η (wickMassShellS m hm η C hC) :=
  schwingerFromTube_osAxioms R_rep S (wickMassShellW m η C hC)
    (wickMassShellTubeExtension m hm η C hC)
    (wickMassShellTubeTranslationInvariant hm η hC)
    (wickMassShellTubeCovariant R_rep hm η hC hC_cov)
    (wickMassShellTubeWickHermiticity S hm M_mode.hη hC hC_herm)
    (wickMassShellTubePCT R_rep hm M_mode.hη hC hC_pct)
    (wickMassShellOSReflectionPositive hm M_mode hC hC_herm)

theorem freeKGPositivity {m : ℝ} (hm : 0 < m) :
    Positivity trivialStarStructure (freeKGW m hm) :=
  wickMassShellPositivity (kgModeData hm) (massiveKGCoeff_data hm)
    (fun _ _ => by simp [massiveKGCoeff, trivialStarStructure])

theorem freeKGOSReflectionPositive {m : ℝ} (hm : 0 < m) :
    OSReflectionPositive trivialStarStructure (freeKGS m hm) :=
  wickMassShellOSReflectionPositive hm (kgModeData hm) (massiveKGCoeff_data hm)
    (fun _ _ => by simp [massiveKGCoeff, trivialStarStructure])

theorem freeKGOSAxioms {m : ℝ} (hm : 0 < m) :
    OSAxioms trivialRep trivialStarStructure 1 (freeKGS m hm) :=
  wickMassShellOSAxioms trivialRep trivialStarStructure hm (kgModeData hm) (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])
    (fun _ _ => by simp [massiveKGCoeff, trivialStarStructure])
    (fun _ _ => by simp [massiveKGCoeff, trivialRep])

theorem freeDiracPositivity {m : ℝ} (hm : 0 < m) :
    Positivity diracStarStructure (freeDiracW m hm) :=
  wickMassShellPositivity (diracModeData hm) (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_herm m)

theorem freeDiracOSReflectionPositive {m : ℝ} (hm : 0 < m) :
    OSReflectionPositive diracStarStructure (freeDiracS m hm) :=
  wickMassShellOSReflectionPositive hm (diracModeData hm) (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_herm m)

theorem freeDiracOSAxioms {m : ℝ} (hm : 0 < m) :
    OSAxioms diracRep diracStarStructure (-1) (freeDiracS m hm) :=
  wickMassShellOSAxioms diracRep diracStarStructure hm (diracModeData hm)
    (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_lorentz m) (diracMassShellCoeff_herm m) (diracMassShellCoeff_pct m)

lemma fockSectorMeasure_zero_univ (ν : ℕ) :
    fockSectorMeasure ν 0 Set.univ = 1 := by
  unfold fockSectorMeasure
  rw [← Set.univ_prod_univ, Measure.prod_prod]
  have h1 : (volume : Measure (Fin 0 → Fin 3 → ℝ)) Set.univ = 1 := by
    rw [volume_pi, Measure.pi_univ]
    simp
  have h2 : (Measure.count : Measure (Fin 0 → Fin ν)) Set.univ = 1 := by
    simp
  rw [h1, h2, mul_one]

instance instIsFiniteMeasureFockSectorZero (ν : ℕ) :
    IsFiniteMeasure (fockSectorMeasure ν 0) :=
  ⟨by rw [fockSectorMeasure_zero_univ]; exact ENNReal.one_lt_top⟩

lemma integral_fockSectorMeasure_zero {ν : ℕ} (g : FockSectorDom ν 0 → ℂ) :
    (∫ x : FockSectorDom ν 0, g x ∂(fockSectorMeasure ν 0)) = g default := by
  have hg : g = fun _ => g default :=
    funext (fun x => congrArg g (Subsingleton.elim x default))
  rw [hg, integral_const]
  simp [Measure.real, fockSectorMeasure_zero_univ]

noncomputable def fockVacuum (ν : ℕ) : FockHilbert ν :=
  liftSectorToFock ν 0 (fun _ => 1) measurable_const (memLp_const (1 : ℂ))

@[simp]
theorem inner_fockVacuum_self (ν : ℕ) :
    ⟪fockVacuum ν, fockVacuum ν⟫_ℂ = 1 := by
  unfold fockVacuum
  rw [inner_liftSectorToFock_eq, integral_fockSectorMeasure_zero]
  simp

@[simp]
theorem norm_fockVacuum (ν : ℕ) :
    ‖fockVacuum ν‖ = 1 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_fockVacuum_self]
  simp

lemma integral_fockMeasure_sectorZero_mul {ν : ℕ} {h : FockOmega ν → ℂ}
    (hh_int : Integrable (fun a : FockOmega ν =>
      (if a.1 = 0 then (1 : ℂ) else 0) * h a) (fockMeasure ν)) :
    (∫ a : FockOmega ν,
      (if a.1 = 0 then (1 : ℂ) else 0) * h a ∂(fockMeasure ν)) = h ⟨0, default⟩ := by
  let F : FockOmega ν → ℂ := fun a => (if a.1 = 0 then (1 : ℂ) else 0) * h a
  have hF_r : ∀ r : ℕ, AEStronglyMeasurable F ((fockSectorMeasure ν r).map (Sigma.mk r)) :=
    fun r => (hh_int.mono_measure (Measure.le_sum _ r)).aestronglyMeasurable
  change ∫ a : FockOmega ν, F a ∂(fockMeasure ν) = _
  unfold fockMeasure
  rw [integral_sum_measure hh_int, tsum_eq_single 0]
  · rw [integral_map (measurable_fockSigmaMk ν 0).aemeasurable (hF_r 0),
        integral_fockSectorMeasure_zero]
    simp [F]
  · intro r hne
    rw [integral_map (measurable_fockSigmaMk ν r).aemeasurable (hF_r r)]
    simp [F, hne]

lemma integrable_sectorZero_mul_of_integrable {ν : ℕ} {h : FockOmega ν → ℂ}
    (hh : Integrable h (fockMeasure ν)) :
    Integrable (fun a : FockOmega ν =>
      (if a.1 = 0 then (1 : ℂ) else 0) * h a) (fockMeasure ν) := by
  have h_eq : (fun a : FockOmega ν => if a.1 = 0 then (1 : ℂ) else 0) =
      sectorToOmega ν 0 (fun _ => (1 : ℂ)) := by
    ext a
    by_cases h0 : a.1 = 0 <;> simp [sectorToOmega, h0]
  have h_ind : Measurable (fun a : FockOmega ν => if a.1 = 0 then (1 : ℂ) else 0) := by
    rw [h_eq]
    exact measurable_sectorToOmega measurable_const
  refine hh.norm.mono' (h_ind.aestronglyMeasurable.mul hh.1)
    (Filter.Eventually.of_forall (fun a => ?_))
  by_cases h0 : a.1 = 0 <;> simp [h0]

theorem inner_fockVacuum_mul_eq_integral {ν : ℕ} (x y : FockHilbert ν) :
    ⟪x, fockVacuum ν⟫_ℂ * ⟪fockVacuum ν, y⟫_ℂ =
      ∫ a : FockOmega ν,
        (if a.1 = 0 then (1 : ℂ) else 0) *
          (star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a) ∂(fockMeasure ν) := by
  have hvac_ae :=
    (memLp_sectorToOmega (ν := ν) (r := 0) (g := fun _ => (1 : ℂ))
      measurable_const (memLp_const (1 : ℂ))).coeFn_toLp
  have hx_eq : ⟪x, fockVacuum ν⟫_ℂ =
      ∫ a : FockOmega ν,
        (if a.1 = 0 then (1 : ℂ) else 0) * star ((x : FockOmega ν → ℂ) a) ∂(fockMeasure ν) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hvac_ae] with a ha
    unfold fockVacuum liftSectorToFock
    rw [ha]
    by_cases h0 : a.1 = 0 <;> simp [RCLike.inner_apply, sectorToOmega, h0]
  have hy_eq : ⟪fockVacuum ν, y⟫_ℂ =
      ∫ a : FockOmega ν,
        (if a.1 = 0 then (1 : ℂ) else 0) * (y : FockOmega ν → ℂ) a ∂(fockMeasure ν) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hvac_ae] with a ha
    unfold fockVacuum liftSectorToFock
    rw [ha]
    by_cases h0 : a.1 = 0 <;> simp [RCLike.inner_apply, sectorToOmega, h0]
  have hx_int : Integrable (fun a : FockOmega ν =>
      (if a.1 = 0 then (1 : ℂ) else 0) * star ((x : FockOmega ν → ℂ) a)) (fockMeasure ν) := by
    refine (L2.integrable_inner (𝕜 := ℂ) x (fockVacuum ν)).congr ?_
    filter_upwards [hvac_ae] with a ha
    unfold fockVacuum liftSectorToFock
    rw [ha]
    by_cases h0 : a.1 = 0 <;> simp [RCLike.inner_apply, sectorToOmega, h0]
  have hy_int : Integrable (fun a : FockOmega ν =>
      (if a.1 = 0 then (1 : ℂ) else 0) * (y : FockOmega ν → ℂ) a) (fockMeasure ν) := by
    refine (L2.integrable_inner (𝕜 := ℂ) (fockVacuum ν) y).congr ?_
    filter_upwards [hvac_ae] with a ha
    unfold fockVacuum liftSectorToFock
    rw [ha]
    by_cases h0 : a.1 = 0 <;> simp [RCLike.inner_apply, sectorToOmega, h0]
  have hxy_int : Integrable (fun a : FockOmega ν =>
      star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a) (fockMeasure ν) := by
    refine (L2.integrable_inner (𝕜 := ℂ) x y).congr (Filter.Eventually.of_forall (fun a => ?_))
    simp [RCLike.inner_apply, mul_comm]
  rw [hx_eq, hy_eq, integral_fockMeasure_sectorZero_mul hx_int,
      integral_fockMeasure_sectorZero_mul hy_int,
      integral_fockMeasure_sectorZero_mul (integrable_sectorZero_mul_of_integrable hxy_int)]

def partialPairingZero : PartialPairing 0 0 where
  unpaired := Fin.elim0
  mate := 1
  strictMono_unpaired a := Fin.elim0 a
  involutive i := Fin.elim0 i
  fixed_iff i := Fin.elim0 i

lemma partialPairing_zero_zero_eq (L : PartialPairing 0 0) :
    L = partialPairingZero :=
  PartialPairing.ext_mate (Subsingleton.elim L.mate 1)

theorem fockMomentumVec_zero_eq_smul_fockVacuum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (α : Fin 0 → ι) (φ : (Fin 0 → Fin 4 → ℝ) → ℂ) (hφ : PartialMomentumBound m 0 φ) :
    fockMomentumVec M_mode hC 0 α φ hφ = φ 0 • fockVacuum M_mode.ν := by
  unfold fockMomentumVec fockVacuum
  rw [Finset.sum_range_one]
  have h_fn : symmSector M_mode.ν 0 η (fockRawSector M_mode 0 α φ) =
      fun _ : FockSectorDom M_mode.ν 0 => φ 0 := by
    ext x
    unfold symmSector fockRawSector
    have h_perm : (Finset.univ : Finset (Equiv.Perm (Fin 0))) = {1} := by
      ext π
      simp [Subsingleton.elim π 1]
    have h_pp : (Finset.univ : Finset (PartialPairing 0 0)) = {partialPairingZero} := by
      ext L
      simp [partialPairing_zero_zero_eq L]
    rw [h_perm, Finset.sum_singleton, permInversions_one, pow_zero, one_mul,
        Nat.factorial_zero, Nat.cast_one, Real.sqrt_one, inv_one, Complex.ofReal_one, one_mul,
        h_pp, Finset.sum_singleton]
    unfold fockPartialTerm
    haveI : IsEmpty partialPairingZero.InternalChord := ⟨fun c => Fin.elim0 c.1⟩
    have h_cross : partialPairingZero.partialCross = 0 := by
      unfold PartialPairing.partialCross PartialPairing.internalCross PartialPairing.openCross
      simp
    have h_vol :
        (volume : Measure (partialPairingZero.InternalChord → Fin 3 → ℝ)) Set.univ = 1 := by
      rw [volume_pi, Measure.pi_univ]
      simp
    have h_ig :
        (fun p_int : partialPairingZero.InternalChord → Fin 3 → ℝ =>
          fockPartialIntWeight m C α partialPairingZero p_int *
            φ (partialPairingZero.partialMomentum m p_int (fockSectorPermEquiv M_mode.ν 0 1 x).1)) =
        fun _ => φ 0 := by
      ext p_int
      have hw : fockPartialIntWeight m C α partialPairingZero p_int = 1 := by
        unfold fockPartialIntWeight
        simp
      have hp :
          partialPairingZero.partialMomentum m p_int (fockSectorPermEquiv M_mode.ν 0 1 x).1 = 0 :=
        Subsingleton.elim _ _
      rw [hw, one_mul, hp]
    rw [h_cross, pow_zero, one_mul, Fin.prod_univ_zero, one_mul, h_ig, integral_const]
    simp [Measure.real, h_vol]
  unfold liftSectorToFock
  have h_smul := (memLp_sectorToOmega (ν := M_mode.ν) (r := 0) (g := fun _ => (1 : ℂ))
    measurable_const (memLp_const (1 : ℂ))).toLp_const_smul (φ 0)
  rw [← h_smul]
  refine MeasureTheory.MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (fun a => ?_))
  by_cases h0 : a.1 = 0 <;> simp [sectorToOmega, h0, h_fn]

@[simp]
theorem fockOSMap_osVacuumConfig {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C) :
    fockOSMap hm M_mode hC (osVacuumConfig ι) = fockVacuum M_mode.ν := by
  unfold fockOSMap osVacuumConfig
  dsimp only
  rw [fockMomentumVec_zero_eq_smul_fockVacuum]
  have h1 : euclidLaplace (euclidOrderedBasePoint 0) 0 = 1 := by
    simp [euclidLaplace]
  rw [h1, one_smul]

@[simp]
theorem fockWightmanMap_wightmanVacuumConfig {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C) :
    fockWightmanMap M_mode hC (wightmanVacuumConfig ι) = fockVacuum M_mode.ν := by
  unfold fockWightmanMap fockSchwartzVec wightmanVacuumConfig wightmanBaseConfig
  dsimp only
  rw [fockMomentumVec_zero_eq_smul_fockVacuum]
  have h1 : minkowskiFourier (momentumWavepacketCompactSchwartz 0 0).val 0 = 1 := by
    have hm : (∫ y : Fin 0 → Fin 4 → ℝ,
        (momentumWavepacketCompactSchwartz 0 0 : SchwartzMap (Fin 0 → Fin 4 → ℝ) ℂ) y) = 1 :=
      integral_momentumWavepacketSchwartz_zero 0
    rw [minkowskiFourier_fin0]
    rwa [integral_fin0] at hm
  rw [h1, one_smul]

lemma lp2_integrable_norm_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (x : Lp ℂ 2 μ) :
    Integrable (fun a : Ω => ‖(x : Ω → ℂ) a‖ ^ 2) μ :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable x)).mp (Lp.memLp x)

lemma lp2_norm_sq_eq_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (x : Lp ℂ 2 μ) :
    ‖x‖ ^ 2 = ∫ a : Ω, ‖(x : Ω → ℂ) a‖ ^ 2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
      ← integral_re (L2.integrable_inner (𝕜 := ℂ) x x)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun a => ?_))
  dsimp only
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
  norm_cast

lemma lp2_integral_norm_mul_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (x y : Lp ℂ 2 μ) :
    (∫ a : Ω, ‖(x : Ω → ℂ) a‖ * ‖(y : Ω → ℂ) a‖ ∂μ) ≤ ‖x‖ * ‖y‖ := by
  let x' : Lp ℝ 2 μ := (Lp.memLp x).norm.toLp (fun a => ‖(x : Ω → ℂ) a‖)
  let y' : Lp ℝ 2 μ := (Lp.memLp y).norm.toLp (fun a => ‖(y : Ω → ℂ) a‖)
  have hx' : ‖x'‖ = ‖x‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm, ← Lp.norm_def]
  have hy' : ‖y'‖ = ‖y‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm, ← Lp.norm_def]
  have h_eq : (∫ a : Ω, ‖(x : Ω → ℂ) a‖ * ‖(y : Ω → ℂ) a‖ ∂μ) = ⟪x', y'⟫_ℝ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(Lp.memLp x).norm.coeFn_toLp, (Lp.memLp y).norm.coeFn_toLp] with a hxa hya
    dsimp [x', y']
    rw [hxa, hya]
    simp [mul_comm]
  rw [h_eq, ← hx', ← hy']
  exact real_inner_le_norm x' y'

lemma memLp_bdd_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m_fn : Ω → ℂ} (hm_meas : Measurable m_fn) {C_bd : ℝ} (_hC_nn : 0 ≤ C_bd)
    (h_bd : ∀ a : Ω, ‖m_fn a‖ ≤ C_bd) {g : Ω → ℂ} (hg : MemLp g 2 μ) :
    MemLp (fun a => m_fn a * g a) 2 μ := by
  have h_meas : AEStronglyMeasurable (fun a => m_fn a * g a) μ :=
    hm_meas.aestronglyMeasurable.mul hg.1
  rw [memLp_two_iff_integrable_sq_norm h_meas]
  have hg_sq : Integrable (fun a => ‖g a‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hg.1).mp hg
  refine (hg_sq.const_mul (C_bd ^ 2)).mono'
    ((continuous_pow 2).comp_aestronglyMeasurable h_meas.norm)
    (Filter.Eventually.of_forall (fun a => ?_))
  rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (h_bd a) 2) (sq_nonneg _)

noncomputable def fockMultLM {ν : ℕ} (m_fn : FockOmega ν → ℂ)
    (hm_meas : Measurable m_fn) {C_bd : ℝ} (hC_nn : 0 ≤ C_bd)
    (h_bd : ∀ a : FockOmega ν, ‖m_fn a‖ ≤ C_bd) :
    FockHilbert ν →ₗ[ℂ] FockHilbert ν where
  toFun x := (memLp_bdd_mul hm_meas hC_nn h_bd (Lp.memLp x)).toLp
    (fun a => m_fn a * (x : FockOmega ν → ℂ) a)
  map_add' x y := by
    have h1 := memLp_bdd_mul hm_meas hC_nn h_bd (Lp.memLp x)
    have h2 := memLp_bdd_mul hm_meas hC_nn h_bd (Lp.memLp y)
    rw [← h1.toLp_add h2]
    refine MeasureTheory.MemLp.toLp_congr _ _ ?_
    filter_upwards [Lp.coeFn_add x y] with a ha
    have ha' : ((x + y : FockHilbert ν) : FockOmega ν → ℂ) a =
        (x : FockOmega ν → ℂ) a + (y : FockOmega ν → ℂ) a := ha
    change m_fn a * ((x + y : FockHilbert ν) : FockOmega ν → ℂ) a = _
    rw [ha', mul_add]
    rfl
  map_smul' c x := by
    have h1 := memLp_bdd_mul hm_meas hC_nn h_bd (Lp.memLp x)
    rw [RingHom.id_apply, ← h1.toLp_const_smul c]
    refine MeasureTheory.MemLp.toLp_congr _ _ ?_
    filter_upwards [Lp.coeFn_smul c x] with a ha
    have ha' : ((c • x : FockHilbert ν) : FockOmega ν → ℂ) a =
        c * (x : FockOmega ν → ℂ) a := ha
    change m_fn a * ((c • x : FockHilbert ν) : FockOmega ν → ℂ) a = _
    rw [ha']
    dsimp only [Pi.smul_apply, smul_eq_mul]
    ring

lemma norm_fockMultLM_le {ν : ℕ} (m_fn : FockOmega ν → ℂ)
    (hm_meas : Measurable m_fn) {C_bd : ℝ} (hC_nn : 0 ≤ C_bd)
    (h_bd : ∀ a : FockOmega ν, ‖m_fn a‖ ≤ C_bd) (x : FockHilbert ν) :
    ‖fockMultLM m_fn hm_meas hC_nn h_bd x‖ ≤ C_bd * ‖x‖ := by
  have h_sq : ‖fockMultLM m_fn hm_meas hC_nn h_bd x‖ ^ 2 ≤ (C_bd * ‖x‖) ^ 2 := by
    rw [lp2_norm_sq_eq_integral, mul_pow, lp2_norm_sq_eq_integral, ← integral_const_mul]
    have h_ae := (memLp_bdd_mul hm_meas hC_nn h_bd (Lp.memLp x)).coeFn_toLp
    refine integral_mono_ae (lp2_integrable_norm_sq _)
      ((lp2_integrable_norm_sq x).const_mul (C_bd ^ 2)) ?_
    filter_upwards [h_ae] with a ha
    dsimp [fockMultLM] at ha ⊢
    rw [ha, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (h_bd a) 2) (sq_nonneg _)
  nlinarith [norm_nonneg (fockMultLM m_fn hm_meas hC_nn h_bd x),
    mul_nonneg hC_nn (norm_nonneg x)]

noncomputable def fockMultCLM {ν : ℕ} (m_fn : FockOmega ν → ℂ)
    (hm_meas : Measurable m_fn) {C_bd : ℝ} (hC_nn : 0 ≤ C_bd)
    (h_bd : ∀ a : FockOmega ν, ‖m_fn a‖ ≤ C_bd) :
    FockHilbert ν →L[ℂ] FockHilbert ν :=
  (fockMultLM m_fn hm_meas hC_nn h_bd).mkContinuous C_bd
    (norm_fockMultLM_le m_fn hm_meas hC_nn h_bd)

lemma fockMultCLM_coeFn {ν : ℕ} (m_fn : FockOmega ν → ℂ)
    (hm_meas : Measurable m_fn) {C_bd : ℝ} (hC_nn : 0 ≤ C_bd)
    (h_bd : ∀ a : FockOmega ν, ‖m_fn a‖ ≤ C_bd) (x : FockHilbert ν) :
    (fockMultCLM m_fn hm_meas hC_nn h_bd x : FockOmega ν → ℂ) =ᶠ[ae (fockMeasure ν)]
      fun a => m_fn a * (x : FockOmega ν → ℂ) a :=
  (memLp_bdd_mul hm_meas hC_nn h_bd (Lp.memLp x)).coeFn_toLp

lemma norm_fockMultCLM_apply_le {ν : ℕ} (m_fn : FockOmega ν → ℂ)
    (hm_meas : Measurable m_fn) {C_bd : ℝ} (hC_nn : 0 ≤ C_bd)
    (h_bd : ∀ a : FockOmega ν, ‖m_fn a‖ ≤ C_bd) (x : FockHilbert ν) :
    ‖fockMultCLM m_fn hm_meas hC_nn h_bd x‖ ≤ C_bd * ‖x‖ :=
  norm_fockMultLM_le m_fn hm_meas hC_nn h_bd x

lemma fockMultCLM_congr {ν : ℕ} {m₁ m₂ : FockOmega ν → ℂ}
    (hm₁ : Measurable m₁) (hm₂ : Measurable m₂)
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hb₁ : ∀ a, ‖m₁ a‖ ≤ C₁) (hb₂ : ∀ a, ‖m₂ a‖ ≤ C₂)
    (heq : ∀ a, m₁ a = m₂ a) :
    fockMultCLM m₁ hm₁ hC₁ hb₁ = fockMultCLM m₂ hm₂ hC₂ hb₂ := by
  ext x : 1
  rw [Lp.ext_iff]
  filter_upwards [fockMultCLM_coeFn m₁ hm₁ hC₁ hb₁ x,
    fockMultCLM_coeFn m₂ hm₂ hC₂ hb₂ x] with a ha₁ ha₂
  rw [ha₁, ha₂, heq a]

lemma fockMultCLM_comp {ν : ℕ}
    {m₁ m₂ : FockOmega ν → ℂ} (hm₁ : Measurable m₁) (hm₂ : Measurable m₂)
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hb₁ : ∀ a, ‖m₁ a‖ ≤ C₁) (hb₂ : ∀ a, ‖m₂ a‖ ≤ C₂) :
    (fockMultCLM m₁ hm₁ hC₁ hb₁).comp (fockMultCLM m₂ hm₂ hC₂ hb₂) =
      fockMultCLM (fun a => m₁ a * m₂ a) (hm₁.mul hm₂) (mul_nonneg hC₁ hC₂)
        (fun a => by rw [norm_mul]; exact mul_le_mul (hb₁ a) (hb₂ a) (norm_nonneg _) hC₁) := by
  ext x : 1
  rw [Lp.ext_iff]
  filter_upwards [fockMultCLM_coeFn m₁ hm₁ hC₁ hb₁ (fockMultCLM m₂ hm₂ hC₂ hb₂ x),
    fockMultCLM_coeFn m₂ hm₂ hC₂ hb₂ x,
    fockMultCLM_coeFn (fun a => m₁ a * m₂ a) (hm₁.mul hm₂) (mul_nonneg hC₁ hC₂)
      (fun a => by rw [norm_mul]; exact mul_le_mul (hb₁ a) (hb₂ a) (norm_nonneg _) hC₁) x]
    with a ha₁ ha₂ ha₁₂
  simp only [ContinuousLinearMap.comp_apply] at ha₁ ⊢
  rw [ha₁, ha₂, ha₁₂, mul_assoc]

lemma fockMultCLM_one (ν : ℕ) :
    fockMultCLM (fun _ : FockOmega ν => (1 : ℂ)) measurable_const zero_le_one
      (fun _ => by simp) = ContinuousLinearMap.id ℂ (FockHilbert ν) := by
  ext x : 1
  rw [Lp.ext_iff]
  filter_upwards [fockMultCLM_coeFn (fun _ : FockOmega ν => (1 : ℂ))
    measurable_const zero_le_one (fun _ => by simp) x] with a ha
  simp [ha]

lemma inner_fockMultCLM_right {ν : ℕ} (m_fn : FockOmega ν → ℂ)
    (hm_meas : Measurable m_fn) {C_bd : ℝ} (hC_nn : 0 ≤ C_bd)
    (h_bd : ∀ a : FockOmega ν, ‖m_fn a‖ ≤ C_bd) (x y : FockHilbert ν) :
    ⟪x, fockMultCLM m_fn hm_meas hC_nn h_bd y⟫_ℂ =
      ∫ a : FockOmega ν,
        m_fn a * (star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a) ∂(fockMeasure ν) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [fockMultCLM_coeFn m_fn hm_meas hC_nn h_bd y] with a ha
  rw [RCLike.inner_apply, ha, ← Complex.star_def]
  ring

lemma inner_fockMultCLM_left {ν : ℕ} (m_fn : FockOmega ν → ℂ)
    (hm_meas : Measurable m_fn) {C_bd : ℝ} (hC_nn : 0 ≤ C_bd)
    (h_bd : ∀ a : FockOmega ν, ‖m_fn a‖ ≤ C_bd) (x y : FockHilbert ν) :
    ⟪fockMultCLM m_fn hm_meas hC_nn h_bd x, y⟫_ℂ =
      ∫ a : FockOmega ν,
        star (m_fn a) *
          (star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a) ∂(fockMeasure ν) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [fockMultCLM_coeFn m_fn hm_meas hC_nn h_bd x] with a ha
  rw [RCLike.inner_apply, ha, map_mul, ← Complex.star_def]
  ring

lemma fockMultCLM_liftSectorToFock {ν r : ℕ} (m_fn : FockOmega ν → ℂ)
    (hm_meas : Measurable m_fn) {C_bd : ℝ} (hC_nn : 0 ≤ C_bd)
    (h_bd : ∀ a : FockOmega ν, ‖m_fn a‖ ≤ C_bd)
    (g : FockSectorDom ν r → ℂ) (hg_meas : Measurable g)
    (hg : MemLp g 2 (fockSectorMeasure ν r)) :
    fockMultCLM m_fn hm_meas hC_nn h_bd (liftSectorToFock ν r g hg_meas hg) =
      liftSectorToFock ν r (fun x => m_fn ⟨r, x⟩ * g x)
        (by exact (hm_meas.comp (measurable_fockSigmaMk ν r)).mul hg_meas)
        (memLp_bdd_mul (hm_meas.comp (measurable_fockSigmaMk ν r)) hC_nn
          (fun x => h_bd ⟨r, x⟩) hg) := by
  have h_prod_meas : Measurable (fun x : FockSectorDom ν r => m_fn ⟨r, x⟩ * g x) :=
    (hm_meas.comp (measurable_fockSigmaMk ν r)).mul hg_meas
  rw [Lp.ext_iff]
  filter_upwards [fockMultCLM_coeFn m_fn hm_meas hC_nn h_bd
      (liftSectorToFock ν r g hg_meas hg),
    (memLp_sectorToOmega hg_meas hg).coeFn_toLp,
    (memLp_sectorToOmega h_prod_meas
      (memLp_bdd_mul (hm_meas.comp (measurable_fockSigmaMk ν r)) hC_nn
        (fun x => h_bd ⟨r, x⟩) hg)).coeFn_toLp] with a ha₁ ha₂ ha₃
  unfold liftSectorToFock at ha₁ ⊢
  rw [ha₁, ha₂, ha₃]
  rcases a with ⟨r', x⟩
  by_cases hr : r' = r
  · subst hr
    simp [sectorToOmega]
  · simp [sectorToOmega, hr]

lemma fockMultCLM_fockVacuum {ν : ℕ} (m_fn : FockOmega ν → ℂ)
    (hm_meas : Measurable m_fn) {C_bd : ℝ} (hC_nn : 0 ≤ C_bd)
    (h_bd : ∀ a : FockOmega ν, ‖m_fn a‖ ≤ C_bd)
    (h0 : m_fn ⟨0, default⟩ = 1) :
    fockMultCLM m_fn hm_meas hC_nn h_bd (fockVacuum ν) = fockVacuum ν := by
  unfold fockVacuum
  rw [fockMultCLM_liftSectorToFock]
  unfold liftSectorToFock
  refine MeasureTheory.MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (fun a => ?_))
  rcases a with ⟨r, x⟩
  by_cases hr : r = 0
  · subst hr
    rw [Subsingleton.elim x default]
    simp [sectorToOmega, h0]
  · simp [sectorToOmega, hr]

noncomputable def fockTotalMomentum {ν : ℕ} (m : ℝ) (a : FockOmega ν) : Fin 4 → ℝ :=
  ∑ i : Fin a.1, massShellVec m (a.2.1 i)

lemma measurable_fockTotalMomentum (ν : ℕ) (m : ℝ) :
    Measurable (fockTotalMomentum (ν := ν) m) := by
  intro U hU
  rw [measurableSet_fockOmega_iff]
  intro r
  have h_sec : Measurable (fun x : FockSectorDom ν r =>
      ∑ i : Fin r, massShellVec m (x.1 i)) :=
    Finset.measurable_sum Finset.univ (fun i _ =>
      (continuous_massShellVec m).measurable.comp ((measurable_pi_apply i).comp measurable_fst))
  exact h_sec hU

@[simp]
lemma fockTotalMomentum_zero {ν : ℕ} (m : ℝ) (x : FockSectorDom ν 0) :
    fockTotalMomentum m ⟨0, x⟩ = 0 := by
  simp [fockTotalMomentum]

lemma fockTotalMomentum_perm {ν r : ℕ} (m : ℝ) (π : Equiv.Perm (Fin r))
    (x : FockSectorDom ν r) :
    fockTotalMomentum m ⟨r, fockSectorPermEquiv ν r π x⟩ = fockTotalMomentum m ⟨r, x⟩ := by
  unfold fockTotalMomentum fockSectorPermEquiv
  dsimp only
  exact Equiv.sum_comp π (fun i => massShellVec m (x.1 i))

lemma partialMomentum_sum_eq {j r : ℕ} (m : ℝ) (L : PartialPairing j r)
    (p_int : L.InternalChord → Fin 3 → ℝ) (k_ext : Fin r → Fin 3 → ℝ) :
    ∑ i : Fin j, L.partialMomentum m p_int k_ext i =
      -∑ a : Fin r, massShellVec m (k_ext a) := by
  rw [← L.partialSlotEquiv.sum_comp, Fintype.sum_sum_type, Fintype.sum_prod_type]
  have h_int :
      (∑ c : L.InternalChord, ∑ s : Fin 2,
        L.partialMomentum m p_int k_ext (L.partialSlotEquiv (Sum.inr (c, s)))) = 0 := by
    refine Finset.sum_eq_zero (fun c _ => ?_)
    rw [Fin.sum_univ_two]
    have hs0 : L.partialSlotEquiv (Sum.inr (c, 0)) = c.1 := rfl
    have hs1 : L.partialSlotEquiv (Sum.inr (c, 1)) = L.mate c.1 := rfl
    rw [hs0, hs1, L.partialMomentum_fst, L.partialMomentum_mate, add_neg_cancel]
  rw [h_int, add_zero, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hsa : L.partialSlotEquiv (Sum.inl a) = L.unpaired a := rfl
  rw [hsa, L.partialMomentum_unpaired]

theorem fockMomentumVec_mul_totalMomentum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (j : ℕ) (α : Fin j → ι)
    {φ₁ φ₂ : (Fin j → Fin 4 → ℝ) → ℂ}
    (hφ₁ : PartialMomentumBound m j φ₁) (hφ₂ : PartialMomentumBound m j φ₂)
    {ψ : (Fin 4 → ℝ) → ℂ} (hψ_meas : Measurable ψ)
    {C_bd : ℝ} (hC_nn : 0 ≤ C_bd)
    (hψ_bd : ∀ a : FockOmega M_mode.ν, ‖ψ (fockTotalMomentum m a)‖ ≤ C_bd)
    (h_eq : ∀ (r : ℕ) (L : PartialPairing j r)
      (p_int : L.InternalChord → Fin 3 → ℝ) (k_ext : Fin r → Fin 3 → ℝ),
      φ₂ (L.partialMomentum m p_int k_ext) =
        ψ (∑ a : Fin r, massShellVec m (k_ext a)) * φ₁ (L.partialMomentum m p_int k_ext)) :
    fockMomentumVec M_mode hC j α φ₂ hφ₂ =
      fockMultCLM (fun a => ψ (fockTotalMomentum m a))
        (hψ_meas.comp (measurable_fockTotalMomentum M_mode.ν m)) hC_nn hψ_bd
        (fockMomentumVec M_mode hC j α φ₁ hφ₁) := by
  unfold fockMomentumVec
  rw [map_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [fockMultCLM_liftSectorToFock]
  unfold liftSectorToFock
  refine MeasureTheory.MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (fun a => ?_))
  rcases a with ⟨r', x⟩
  by_cases hr : r' = r
  · subst hr
    simp only [sectorToOmega_sigmaMk_eq]
    unfold symmSector
    have h_sum :
        (∑ π : Equiv.Perm (Fin r'),
          η ^ permInversions π *
            fockRawSector M_mode r' α φ₂ (fockSectorPermEquiv M_mode.ν r' π x)) =
        ∑ π : Equiv.Perm (Fin r'),
          ψ (fockTotalMomentum m ⟨r', x⟩) *
            (η ^ permInversions π *
              fockRawSector M_mode r' α φ₁ (fockSectorPermEquiv M_mode.ν r' π x)) := by
      refine Finset.sum_congr rfl (fun π _ => ?_)
      rw [← fockTotalMomentum_perm m π x]
      unfold fockRawSector
      have h_raw :
          (∑ L : PartialPairing j r',
            fockPartialTerm M_mode α φ₂ L (fockSectorPermEquiv M_mode.ν r' π x)) =
          ψ (fockTotalMomentum m ⟨r', fockSectorPermEquiv M_mode.ν r' π x⟩) *
            ∑ L : PartialPairing j r',
              fockPartialTerm M_mode α φ₁ L (fockSectorPermEquiv M_mode.ν r' π x) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun L _ => ?_)
        unfold fockPartialTerm fockTotalMomentum
        have h_int :
            (∫ p_int : L.InternalChord → Fin 3 → ℝ,
              fockPartialIntWeight m C α L p_int *
                φ₂ (L.partialMomentum m p_int (fockSectorPermEquiv M_mode.ν r' π x).1)) =
            ψ (∑ a : Fin r', massShellVec m ((fockSectorPermEquiv M_mode.ν r' π x).1 a)) *
              ∫ p_int : L.InternalChord → Fin 3 → ℝ,
                fockPartialIntWeight m C α L p_int *
                  φ₁ (L.partialMomentum m p_int (fockSectorPermEquiv M_mode.ν r' π x).1) := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall (fun p_int => ?_))
          dsimp only
          rw [h_eq r' L p_int (fockSectorPermEquiv M_mode.ν r' π x).1]
          ring
        rw [h_int]
        ring
      rw [h_raw]
      ring
    rw [h_sum, ← Finset.mul_sum]
    ring
  · simp [sectorToOmega, hr]

noncomputable def fockEnergy {ν : ℕ} (m : ℝ) (a : FockOmega ν) : ℝ :=
  fockTotalMomentum m a 0

lemma fockEnergy_eq_sum {ν : ℕ} (m : ℝ) (a : FockOmega ν) :
    fockEnergy m a = ∑ i : Fin a.1, massShellEnergy m (a.2.1 i) := by
  simp [fockEnergy, fockTotalMomentum, massShellVec]

lemma measurable_fockEnergy (ν : ℕ) (m : ℝ) :
    Measurable (fockEnergy (ν := ν) m) :=
  (measurable_pi_apply 0).comp (measurable_fockTotalMomentum ν m)

lemma fockEnergy_nonneg {ν : ℕ} (m : ℝ) (a : FockOmega ν) :
    0 ≤ fockEnergy m a := by
  rw [fockEnergy_eq_sum]
  exact Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)

@[simp]
lemma fockEnergy_zero {ν : ℕ} (m : ℝ) (x : FockSectorDom ν 0) :
    fockEnergy m ⟨0, x⟩ = 0 := by
  simp [fockEnergy]

lemma fockEnergy_ge_mass_of_ne_zero {ν : ℕ} {m : ℝ} (hm : 0 < m)
    {a : FockOmega ν} (ha : a.1 ≠ 0) :
    m ≤ fockEnergy m a := by
  rcases a with ⟨r, x⟩
  dsimp at ha
  cases r with
  | zero => exact False.elim (ha rfl)
  | succ r' =>
    rw [fockEnergy_eq_sum]
    have h0 : (0 : Fin (r' + 1)) ∈ (Finset.univ : Finset (Fin (r' + 1))) := Finset.mem_univ 0
    have h_le : massShellEnergy m (x.1 0) ≤
        ∑ i : Fin (r' + 1), massShellEnergy m (x.1 i) :=
      Finset.single_le_sum (f := fun i => massShellEnergy m (x.1 i))
        (fun i _ => Real.sqrt_nonneg _) h0
    exact (massShellEnergy_ge_mass hm (x.1 0)).trans h_le

noncomputable def fockSemigroup {ν : ℕ} (m : ℝ) (z : ℂ) (hz : z ∈ rightHalfPlane) :
    FockHilbert ν →L[ℂ] FockHilbert ν :=
  fockMultCLM (fun a => laplaceExp (fockEnergy m a) z)
    ((differentiable_laplaceExp 1 |>.continuous |> fun _ =>
      (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).measurable).comp
      (measurable_fockEnergy ν m))
    zero_le_one
    (fun a => norm_laplaceExp_le_one (fockEnergy_nonneg m a) hz)

@[simp]
lemma fockSemigroup_zero {ν : ℕ} (m : ℝ) :
    fockSemigroup (ν := ν) m 0 zero_mem_rightHalfPlane =
      ContinuousLinearMap.id ℂ (FockHilbert ν) := by
  rw [← fockMultCLM_one ν]
  exact fockMultCLM_congr _ _ zero_le_one zero_le_one _ _ (fun a => laplaceExp_zero_right _)

lemma fockSemigroup_add {ν : ℕ} (m : ℝ) {z₁ z₂ : ℂ}
    (h₁ : z₁ ∈ rightHalfPlane) (h₂ : z₂ ∈ rightHalfPlane) :
    fockSemigroup (ν := ν) m (z₁ + z₂) (add_mem_rightHalfPlane h₁ h₂) =
      (fockSemigroup m z₁ h₁).comp (fockSemigroup m z₂ h₂) := by
  unfold fockSemigroup
  rw [fockMultCLM_comp]
  exact fockMultCLM_congr _ _ zero_le_one _ _ _ (fun a => laplaceExp_add (fockEnergy m a) z₁ z₂)

@[simp]
lemma fockSemigroup_fockVacuum {ν : ℕ} (m : ℝ) (z : ℂ) (hz : z ∈ rightHalfPlane) :
    fockSemigroup m z hz (fockVacuum ν) = fockVacuum ν := by
  unfold fockSemigroup
  exact fockMultCLM_fockVacuum _ _ zero_le_one _ (by simp)

lemma norm_fockSemigroup_le {ν : ℕ} (m : ℝ) (z : ℂ) (hz : z ∈ rightHalfPlane)
    (x : FockHilbert ν) :
    ‖fockSemigroup m z hz x‖ ≤ ‖x‖ := by
  unfold fockSemigroup
  simpa using norm_fockMultCLM_apply_le _ _ zero_le_one _ x

lemma inner_fockSemigroup_eq {ν : ℕ} (m : ℝ) (z : ℂ) (hz : z ∈ rightHalfPlane)
    (x y : FockHilbert ν) :
    ⟪x, fockSemigroup m z hz y⟫_ℂ =
      ∫ a : FockOmega ν,
        laplaceExp (fockEnergy m a) z *
          (star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a) ∂(fockMeasure ν) := by
  unfold fockSemigroup
  exact inner_fockMultCLM_right _ _ zero_le_one _ x y

lemma fockSemigroup_adjoint_symm {ν : ℕ} (m : ℝ) (z : ℂ) (hz : z ∈ rightHalfPlane)
    (x y : FockHilbert ν) :
    ⟪fockSemigroup m z hz x, y⟫_ℂ =
      ⟪x, fockSemigroup m (star z) (star_mem_rightHalfPlane hz) y⟫_ℂ := by
  unfold fockSemigroup
  rw [inner_fockMultCLM_left, inner_fockMultCLM_right]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun a => ?_))
  dsimp only
  rw [laplaceExp_star]

noncomputable def fockSpatialPhase (b : Fin 3 → ℝ) (P : Fin 4 → ℝ) : ℂ :=
  Complex.exp (-Complex.I * ((P 1 : ℂ) * (b 0 : ℂ) + (P 2 : ℂ) * (b 1 : ℂ) +
    (P 3 : ℂ) * (b 2 : ℂ)))

lemma continuous_fockSpatialPhase (b : Fin 3 → ℝ) :
    Continuous (fockSpatialPhase b) := by
  unfold fockSpatialPhase
  have hc : ∀ μ : Fin 4, Continuous (fun P : Fin 4 → ℝ => (P μ : ℂ)) :=
    fun μ => Complex.continuous_ofReal.comp (continuous_apply μ)
  exact Complex.continuous_exp.comp
    (continuous_const.mul
      ((((hc 1).mul continuous_const).add ((hc 2).mul continuous_const)).add
        ((hc 3).mul continuous_const)))

lemma norm_fockSpatialPhase (b : Fin 3 → ℝ) (P : Fin 4 → ℝ) :
    ‖fockSpatialPhase b P‖ = 1 := by
  unfold fockSpatialPhase
  rw [Complex.norm_exp]
  have hre : (-Complex.I * ((P 1 : ℂ) * (b 0 : ℂ) + (P 2 : ℂ) * (b 1 : ℂ) +
      (P 3 : ℂ) * (b 2 : ℂ))).re = 0 := by
    simp [Complex.mul_re, Complex.add_re]
  rw [hre, Real.exp_zero]

noncomputable def fockSpatialTranslate {ν : ℕ} (m : ℝ) (b : Fin 3 → ℝ) :
    FockHilbert ν →L[ℂ] FockHilbert ν :=
  fockMultCLM (fun a => fockSpatialPhase b (fockTotalMomentum m a))
    ((continuous_fockSpatialPhase b).measurable.comp (measurable_fockTotalMomentum ν m))
    zero_le_one
    (fun a => (norm_fockSpatialPhase b (fockTotalMomentum m a)).le)

lemma fockSpatialTranslate_comm_fockSemigroup {ν : ℕ} (m : ℝ) (b : Fin 3 → ℝ)
    (z : ℂ) (hz : z ∈ rightHalfPlane) :
    (fockSpatialTranslate (ν := ν) m b).comp (fockSemigroup m z hz) =
      (fockSemigroup m z hz).comp (fockSpatialTranslate m b) := by
  unfold fockSpatialTranslate fockSemigroup
  rw [fockMultCLM_comp, fockMultCLM_comp]
  exact fockMultCLM_congr _ _ _ _ _ _ (fun a => mul_comm _ _)

theorem fockOSMap_osConfigTimeShift {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (τ : ℝ) (hτ : 0 ≤ τ) (A : OSConfig ι) :
    fockOSMap hm M_mode hC (osConfigTimeShift τ hτ A) =
      fockSemigroup m (τ : ℂ) (ofReal_mem_rightHalfPlane hτ) (fockOSMap hm M_mode hC A) := by
  rcases A with ⟨j, α, x, hx⟩
  unfold fockOSMap osConfigTimeShift fockSemigroup
  dsimp only
  let ψ : (Fin 4 → ℝ) → ℂ := fun P => laplaceExp (P 0) (τ : ℂ)
  have hψ_meas : Measurable ψ :=
    (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply 0)))).measurable
  have h_eq : ∀ (r : ℕ) (L : PartialPairing j r)
      (p_int : L.InternalChord → Fin 3 → ℝ) (k_ext : Fin r → Fin 3 → ℝ),
      euclidLaplace (fun i => x i + euclidTimeVec τ) (L.partialMomentum m p_int k_ext) =
        ψ (∑ a : Fin r, massShellVec m (k_ext a)) *
          euclidLaplace x (L.partialMomentum m p_int k_ext) := by
    intro r L p_int k_ext
    unfold euclidLaplace ψ laplaceExp
    rw [← Complex.exp_add]
    congr 1
    have h_sum0 : (∑ i : Fin j, L.partialMomentum m p_int k_ext i 0) =
        -(∑ a : Fin r, massShellVec m (k_ext a)) 0 := by
      have h := congrArg (fun v : Fin 4 → ℝ => v 0)
        (partialMomentum_sum_eq m L p_int k_ext)
      simpa using h
    have h_term : ∀ i : Fin j,
        (L.partialMomentum m p_int k_ext i 0 : ℂ) * ((x i + euclidTimeVec τ) 0 : ℂ) +
          Complex.I * ((L.partialMomentum m p_int k_ext i 1 : ℂ) *
              ((x i + euclidTimeVec τ) 1 : ℂ) +
            (L.partialMomentum m p_int k_ext i 2 : ℂ) * ((x i + euclidTimeVec τ) 2 : ℂ) +
            (L.partialMomentum m p_int k_ext i 3 : ℂ) * ((x i + euclidTimeVec τ) 3 : ℂ)) =
        (L.partialMomentum m p_int k_ext i 0 : ℂ) * (τ : ℂ) +
          ((L.partialMomentum m p_int k_ext i 0 : ℂ) * (x i 0 : ℂ) +
            Complex.I * ((L.partialMomentum m p_int k_ext i 1 : ℂ) * (x i 1 : ℂ) +
              (L.partialMomentum m p_int k_ext i 2 : ℂ) * (x i 2 : ℂ) +
              (L.partialMomentum m p_int k_ext i 3 : ℂ) * (x i 3 : ℂ))) := by
      intro i
      simp [euclidTimeVec]
      ring
    simp_rw [h_term]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Complex.ofReal_sum, h_sum0,
        Complex.ofReal_neg]
    ring
  rw [fockMomentumVec_mul_totalMomentum M_mode hC j α
    (partialMomentumBound_euclidLaplace hm hx)
    (partialMomentumBound_euclidLaplace hm (timeShift_mem_posOrderedEuclidN j hx hτ))
    hψ_meas zero_le_one
    (fun a => norm_laplaceExp_le_one (fockEnergy_nonneg m a) (ofReal_mem_rightHalfPlane hτ))
    h_eq]
  exact ContinuousLinearMap.ext_iff.mp
    (fockMultCLM_congr _ _ zero_le_one zero_le_one _ _ (fun _ => rfl)) _

theorem fockOSMap_osConfigSpatialShift {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (b : Fin 3 → ℝ) (A : OSConfig ι) :
    fockOSMap hm M_mode hC (osConfigSpatialShift b A) =
      fockSpatialTranslate m b (fockOSMap hm M_mode hC A) := by
  rcases A with ⟨j, α, x, hx⟩
  unfold fockOSMap osConfigSpatialShift fockSpatialTranslate
  dsimp only
  have h_eq : ∀ (r : ℕ) (L : PartialPairing j r)
      (p_int : L.InternalChord → Fin 3 → ℝ) (k_ext : Fin r → Fin 3 → ℝ),
      euclidLaplace (fun i => x i + euclidSpatialVec b) (L.partialMomentum m p_int k_ext) =
        fockSpatialPhase b (∑ a : Fin r, massShellVec m (k_ext a)) *
          euclidLaplace x (L.partialMomentum m p_int k_ext) := by
    intro r L p_int k_ext
    unfold euclidLaplace fockSpatialPhase
    rw [← Complex.exp_add]
    congr 1
    have h_sum_μ : ∀ μ : Fin 4,
        (∑ i : Fin j, L.partialMomentum m p_int k_ext i μ) =
          -(∑ a : Fin r, massShellVec m (k_ext a)) μ := by
      intro μ
      have h := congrArg (fun v : Fin 4 → ℝ => v μ)
        (partialMomentum_sum_eq m L p_int k_ext)
      simpa using h
    have h_term : ∀ i : Fin j,
        (L.partialMomentum m p_int k_ext i 0 : ℂ) * ((x i + euclidSpatialVec b) 0 : ℂ) +
          Complex.I * ((L.partialMomentum m p_int k_ext i 1 : ℂ) *
              ((x i + euclidSpatialVec b) 1 : ℂ) +
            (L.partialMomentum m p_int k_ext i 2 : ℂ) *
              ((x i + euclidSpatialVec b) 2 : ℂ) +
            (L.partialMomentum m p_int k_ext i 3 : ℂ) *
              ((x i + euclidSpatialVec b) 3 : ℂ)) =
        Complex.I * ((L.partialMomentum m p_int k_ext i 1 : ℂ) * (b 0 : ℂ) +
            (L.partialMomentum m p_int k_ext i 2 : ℂ) * (b 1 : ℂ) +
            (L.partialMomentum m p_int k_ext i 3 : ℂ) * (b 2 : ℂ)) +
          ((L.partialMomentum m p_int k_ext i 0 : ℂ) * (x i 0 : ℂ) +
            Complex.I * ((L.partialMomentum m p_int k_ext i 1 : ℂ) * (x i 1 : ℂ) +
              (L.partialMomentum m p_int k_ext i 2 : ℂ) * (x i 2 : ℂ) +
              (L.partialMomentum m p_int k_ext i 3 : ℂ) * (x i 3 : ℂ))) := by
      intro i
      have hb0 : euclidSpatialVec b 0 = 0 := rfl
      have hb1 : euclidSpatialVec b 1 = b 0 := rfl
      have hb2 : euclidSpatialVec b 2 = b 1 := rfl
      have hb3 : euclidSpatialVec b 3 = b 2 := rfl
      simp only [Pi.add_apply, hb0, hb1, hb2, hb3, add_zero]
      push_cast
      ring
    simp_rw [h_term]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
        Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul,
        ← Complex.ofReal_sum, ← Complex.ofReal_sum, ← Complex.ofReal_sum,
        h_sum_μ 1, h_sum_μ 2, h_sum_μ 3,
        Complex.ofReal_neg, Complex.ofReal_neg, Complex.ofReal_neg]
    ring
  exact fockMomentumVec_mul_totalMomentum M_mode hC j α
    (partialMomentumBound_euclidLaplace hm hx)
    (partialMomentumBound_euclidLaplace hm (spatialShift_mem_posOrderedEuclidN j hx b))
    (continuous_fockSpatialPhase b).measurable zero_le_one
    (fun a => (norm_fockSpatialPhase b (fockTotalMomentum m a)).le) h_eq

theorem norm_inner_fockSemigroup_sub_fockVacuum_le {ν : ℕ} {m : ℝ} (hm : 0 < m)
    {τ : ℝ} (hτ : 0 ≤ τ) (x y : FockHilbert ν) :
    ‖⟪x, fockSemigroup m (τ : ℂ) (ofReal_mem_rightHalfPlane hτ) y⟫_ℂ -
        ⟪x, fockVacuum ν⟫_ℂ * ⟪fockVacuum ν, y⟫_ℂ‖ ≤
      ‖x‖ * ‖y‖ * Real.exp (-(m * τ)) := by
  have hxy_int : Integrable (fun a : FockOmega ν =>
      star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a) (fockMeasure ν) := by
    refine (L2.integrable_inner (𝕜 := ℂ) x y).congr (Filter.Eventually.of_forall (fun a => ?_))
    simp [RCLike.inner_apply, mul_comm]
  have h1_int : Integrable (fun a : FockOmega ν =>
      laplaceExp (fockEnergy m a) (τ : ℂ) *
        (star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a)) (fockMeasure ν) := by
    have h_meas : Measurable (fun a : FockOmega ν => laplaceExp (fockEnergy m a) (τ : ℂ)) :=
      (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).measurable.comp
        (measurable_fockEnergy ν m)
    refine hxy_int.norm.mono' (h_meas.aestronglyMeasurable.mul hxy_int.1)
      (Filter.Eventually.of_forall (fun a => ?_))
    rw [norm_mul]
    calc ‖laplaceExp (fockEnergy m a) (τ : ℂ)‖ *
            ‖star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a‖
        ≤ 1 * ‖star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a‖ :=
          mul_le_mul_of_nonneg_right
            (norm_laplaceExp_le_one (fockEnergy_nonneg m a) (ofReal_mem_rightHalfPlane hτ))
            (norm_nonneg _)
      _ = _ := one_mul _
  have h0_int := integrable_sectorZero_mul_of_integrable hxy_int
  rw [inner_fockSemigroup_eq, inner_fockVacuum_mul_eq_integral, ← integral_sub h1_int h0_int]
  have h_pt : ∀ a : FockOmega ν,
      ‖laplaceExp (fockEnergy m a) (τ : ℂ) *
          (star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a) -
        (if a.1 = 0 then (1 : ℂ) else 0) *
          (star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a)‖ ≤
      Real.exp (-(m * τ)) * (‖(x : FockOmega ν → ℂ) a‖ * ‖(y : FockOmega ν → ℂ) a‖) := by
    intro a
    rw [← sub_mul, norm_mul, norm_mul, norm_star]
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    rcases a with ⟨r, z⟩
    by_cases hr : r = 0
    · subst hr
      simp only [fockEnergy_zero, laplaceExp_zero_left, ↓reduceIte, sub_self, norm_zero]
      exact (Real.exp_pos _).le
    · simp only [hr, ↓reduceIte, sub_zero, norm_laplaceExp, Complex.ofReal_re]
      exact Real.exp_le_exp.mpr
        (by nlinarith [fockEnergy_ge_mass_of_ne_zero hm (a := ⟨r, z⟩) hr])
  calc ‖∫ a : FockOmega ν,
          (laplaceExp (fockEnergy m a) (τ : ℂ) *
              (star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a) -
            (if a.1 = 0 then (1 : ℂ) else 0) *
              (star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a)) ∂(fockMeasure ν)‖
      ≤ ∫ a : FockOmega ν,
          ‖laplaceExp (fockEnergy m a) (τ : ℂ) *
              (star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a) -
            (if a.1 = 0 then (1 : ℂ) else 0) *
              (star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a)‖ ∂(fockMeasure ν) :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ a : FockOmega ν,
          Real.exp (-(m * τ)) *
            (‖(x : FockOmega ν → ℂ) a‖ * ‖(y : FockOmega ν → ℂ) a‖) ∂(fockMeasure ν) := by
        have h_norm_int : Integrable (fun a : FockOmega ν =>
            ‖(x : FockOmega ν → ℂ) a‖ * ‖(y : FockOmega ν → ℂ) a‖) (fockMeasure ν) := by
          refine hxy_int.norm.congr (Filter.Eventually.of_forall (fun a => ?_))
          simp
        exact integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
          (h_norm_int.const_mul _) (Filter.Eventually.of_forall h_pt)
    _ = Real.exp (-(m * τ)) *
          ∫ a : FockOmega ν,
            ‖(x : FockOmega ν → ℂ) a‖ * ‖(y : FockOmega ν → ℂ) a‖ ∂(fockMeasure ν) :=
        integral_const_mul _ _
    _ ≤ Real.exp (-(m * τ)) * (‖x‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left (lp2_integral_norm_mul_le x y) (Real.exp_pos _).le
    _ = ‖x‖ * ‖y‖ * Real.exp (-(m * τ)) := by ring

theorem wickMassShellOS_exponential_cluster {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    {τ : ℝ} (hτ : 0 ≤ τ) (A B : OSConfig ι) :
    ‖osKernel S (wickMassShellS m hm η C hC) A (osConfigTimeShift τ hτ B) -
        osKernel S (wickMassShellS m hm η C hC) A (osVacuumConfig ι) *
          osKernel S (wickMassShellS m hm η C hC) (osVacuumConfig ι) B‖ ≤
      ‖fockOSMap hm M_mode hC A‖ * ‖fockOSMap hm M_mode hC B‖ * Real.exp (-(m * τ)) := by
  rw [← inner_fockOSMap_eq_osKernel hm M_mode hC hC_herm A (osConfigTimeShift τ hτ B),
      ← inner_fockOSMap_eq_osKernel hm M_mode hC hC_herm A (osVacuumConfig ι),
      ← inner_fockOSMap_eq_osKernel hm M_mode hC hC_herm (osVacuumConfig ι) B,
      fockOSMap_osConfigTimeShift hm M_mode hC τ hτ B,
      fockOSMap_osVacuumConfig hm M_mode hC]
  exact norm_inner_fockSemigroup_sub_fockVacuum_le hm hτ
    (fockOSMap hm M_mode hC A) (fockOSMap hm M_mode hC B)

theorem wickMassShellOSTimeCluster {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (D : OSReflectionPositiveData R_rep S)
    (hD : D.𝒮 = wickMassShellS m hm η C hC) :
    OSTimeClusterDecomposition D := by
  intro A B
  rw [hD, tendsto_iff_norm_sub_tendsto_zero]
  have h_tendsto :
      Tendsto (fun τ : ℝ =>
        ‖fockOSMap hm M_mode hC A‖ * ‖fockOSMap hm M_mode hC B‖ *
          Real.exp (-(m * max τ 0))) atTop (𝓝 0) := by
    have h_lin : Tendsto (fun τ : ℝ => -(m * max τ 0)) atTop atBot := by
      have h_max : Filter.Tendsto (fun τ : ℝ => max τ 0) atTop atTop :=
        tendsto_atTop_mono (fun τ => le_max_left τ 0) tendsto_id
      exact tendsto_neg_atTop_atBot.comp (Filter.Tendsto.const_mul_atTop hm h_max)
    simpa only [Function.comp_def, mul_zero] using
      tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp h_lin)
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun τ => wickMassShellOS_exponential_cluster hm M_mode hC hC_herm (le_max_right τ 0) A B)
    h_tendsto

theorem freeKGOSTimeCluster {m : ℝ} (hm : 0 < m) :
    OSTimeClusterDecomposition (freeKGOSAxioms hm).toReflectionPositiveData :=
  wickMassShellOSTimeCluster hm (kgModeData hm) (massiveKGCoeff_data hm)
    (fun _ _ => by simp [massiveKGCoeff, trivialStarStructure]) _ rfl

theorem freeDiracOSTimeCluster {m : ℝ} (hm : 0 < m) :
    OSTimeClusterDecomposition (freeDiracOSAxioms hm).toReflectionPositiveData :=
  wickMassShellOSTimeCluster hm (diracModeData hm) (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_herm m) _ rfl

noncomputable def wavepacketOSPreLM {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H) :
    OSPreHilbertSpace D →ₗ[ℂ] H :=
  (Finsupp.lsum ℂ (fun A => LinearMap.toSpanSingleton ℂ H (Φ A))).comp
    (OSPreHilbertSpace.equivFinsupp D).toLinearMap

@[simp]
lemma wavepacketOSPreLM_osBasisPre {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H) (A : OSConfig ι) :
    wavepacketOSPreLM D Φ (osBasisPre D A) = Φ A := by
  dsimp [wavepacketOSPreLM, osBasisPre, OSPreHilbertSpace.equivFinsupp]
  simp

theorem inner_wavepacketOSPreLM {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B)
    (Ψ₁ Ψ₂ : OSPreHilbertSpace D) :
    ⟪wavepacketOSPreLM D Φ Ψ₁, wavepacketOSPreLM D Φ Ψ₂⟫_ℂ = ⟪Ψ₁, Ψ₂⟫_ℂ := by
  let L := wavepacketOSPreLM D Φ
  have hL : ∀ X : OSPreHilbertSpace D,
      L X = ∑ A ∈ X.toFinsupp.support, X.toFinsupp A • Φ A := by
    intro X
    conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D X]
    rw [map_finsuppSum]
    unfold Finsupp.sum
    refine Finset.sum_congr rfl (fun A _ => ?_)
    dsimp only
    rw [L.map_smul, wavepacketOSPreLM_osBasisPre]
  have hX : ∀ X : OSPreHilbertSpace D,
      X = ∑ A ∈ X.toFinsupp.support, X.toFinsupp A • osBasisPre D A := by
    intro X
    conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D X]
    rfl
  rw [hL Ψ₁, hL Ψ₂]
  conv_rhs => rw [hX Ψ₁, hX Ψ₂]
  rw [sum_inner (𝕜 := ℂ), sum_inner (𝕜 := ℂ)]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  rw [inner_smul_left, inner_smul_left, inner_sum (𝕜 := ℂ), inner_sum (𝕜 := ℂ)]
  congr 1
  refine Finset.sum_congr rfl (fun B _ => ?_)
  rw [inner_smul_right, inner_smul_right, h_ker A B, inner_osBasisPre]

theorem norm_wavepacketOSPreLM {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B)
    (Ψ : OSPreHilbertSpace D) :
    ‖wavepacketOSPreLM D Φ Ψ‖ = ‖Ψ‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_wavepacketOSPreLM D Φ h_ker Ψ Ψ]

noncomputable def wavepacketOSPreCLM {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B) :
    OSPreHilbertSpace D →L[ℂ] H :=
  (wavepacketOSPreLM D Φ).mkContinuous 1 (fun Ψ => by
    rw [one_mul, norm_wavepacketOSPreLM D Φ h_ker Ψ])

noncomputable def wavepacketOSCLM {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B) :
    OSHilbert D →L[ℂ] H :=
  (wavepacketOSPreCLM D Φ h_ker).extend (toOSHilbert D)

@[simp]
lemma wavepacketOSCLM_toOSHilbert {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B)
    (Ψ : OSPreHilbertSpace D) :
    wavepacketOSCLM D Φ h_ker (toOSHilbert D Ψ) = wavepacketOSPreLM D Φ Ψ :=
  (wavepacketOSPreCLM D Φ h_ker).extend_eq
    UniformSpace.Completion.isDenseInducing_coe.dense
    (UniformSpace.Completion.isUniformInducing_coe _) Ψ

@[simp]
theorem wavepacketOSCLM_osBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B)
    (A : OSConfig ι) :
    wavepacketOSCLM D Φ h_ker (osBasis D A) = Φ A := by
  dsimp [osBasis]
  rw [wavepacketOSCLM_toOSHilbert, wavepacketOSPreLM_osBasisPre]

@[simp]
theorem wavepacketOSCLM_osVacuum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B) :
    wavepacketOSCLM D Φ h_ker (osVacuum D) = Φ (osVacuumConfig ι) :=
  wavepacketOSCLM_osBasis D Φ h_ker (osVacuumConfig ι)

theorem inner_wavepacketOSCLM {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B)
    (x y : OSHilbert D) :
    ⟪wavepacketOSCLM D Φ h_ker x, wavepacketOSCLM D Φ h_ker y⟫_ℂ = ⟪x, y⟫_ℂ := by
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ₁ Ψ₂ =>
    change ⟪wavepacketOSCLM D Φ h_ker (toOSHilbert D Ψ₁),
        wavepacketOSCLM D Φ h_ker (toOSHilbert D Ψ₂)⟫_ℂ =
      ⟪toOSHilbert D Ψ₁, toOSHilbert D Ψ₂⟫_ℂ
    rw [wavepacketOSCLM_toOSHilbert, wavepacketOSCLM_toOSHilbert,
        inner_toOSHilbert, inner_wavepacketOSPreLM D Φ h_ker Ψ₁ Ψ₂]

theorem norm_wavepacketOSCLM {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B)
    (x : OSHilbert D) :
    ‖wavepacketOSCLM D Φ h_ker x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_wavepacketOSCLM D Φ h_ker x x]

noncomputable def wavepacketOSLinearIsometry {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B) :
    OSHilbert D →ₗᵢ[ℂ] H where
  toLinearMap := (wavepacketOSCLM D Φ h_ker).toLinearMap
  norm_map' := norm_wavepacketOSCLM D Φ h_ker

@[simp]
theorem wavepacketOSLinearIsometry_osVacuum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B) :
    wavepacketOSLinearIsometry D Φ h_ker (osVacuum D) = Φ (osVacuumConfig ι) :=
  wavepacketOSCLM_osVacuum D Φ h_ker

theorem wavepacketOSLinearIsometry_intertwines_contraction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hcontr : OSContractionCondition D)
    (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B)
    (τ : ℝ) (hτ : 0 ≤ τ) (T : H →L[ℂ] H)
    (h_T : ∀ A : OSConfig ι, Φ (osConfigTimeShift τ hτ A) = T (Φ A))
    (x : OSHilbert D) :
    wavepacketOSLinearIsometry D Φ h_ker (osContractionSemigroup D hcontr τ hτ x) =
      T (wavepacketOSLinearIsometry D Φ h_ker x) := by
  let J := wavepacketOSCLM D Φ h_ker
  change J (osContractionSemigroup D hcontr τ hτ x) = T (J x)
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change J (osContractionSemigroup D hcontr τ hτ (toOSHilbert D Ψ)) =
      T (J (toOSHilbert D Ψ))
    rw [osContractionSemigroup_toOSHilbert, wavepacketOSCLM_toOSHilbert,
        wavepacketOSCLM_toOSHilbert]
    conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D Ψ]
    conv_rhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D Ψ]
    unfold osTimeShiftLM Finsupp.sum
    rw [map_sum, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul, T.map_smul,
        osLiftConfigMap_osBasisPre, wavepacketOSPreLM_osBasisPre,
        wavepacketOSPreLM_osBasisPre, h_T]

theorem wavepacketOSLinearIsometry_intertwines_spatial
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B)
    (b : Fin 3 → ℝ) (U : H →L[ℂ] H)
    (h_U : ∀ A : OSConfig ι, Φ (osConfigSpatialShift b A) = U (Φ A))
    (x : OSHilbert D) :
    wavepacketOSLinearIsometry D Φ h_ker (osSpatialTranslate D htrans b x) =
      U (wavepacketOSLinearIsometry D Φ h_ker x) := by
  let J := wavepacketOSCLM D Φ h_ker
  change J (osSpatialTranslate D htrans b x) = U (J x)
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change J (osSpatialTranslate D htrans b (toOSHilbert D Ψ)) =
      U (J (toOSHilbert D Ψ))
    rw [osSpatialTranslate_toOSHilbert, wavepacketOSCLM_toOSHilbert,
        wavepacketOSCLM_toOSHilbert]
    conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D Ψ]
    conv_rhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D Ψ]
    unfold osSpatialTranslateLM Finsupp.sum
    rw [map_sum, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul, U.map_smul,
        osLiftConfigMap_osBasisPre, wavepacketOSPreLM_osBasisPre,
        wavepacketOSPreLM_osBasisPre, h_U]

lemma eq_zero_on_rightHalfPlane_of_real_zero {g : ℂ → ℂ}
    (hg_holo : DifferentiableOn ℂ g {z : ℂ | 0 < z.re})
    (hg_cont : ContinuousOn g rightHalfPlane)
    (hg_real : ∀ (τ : ℝ), 0 ≤ τ → g (τ : ℂ) = 0) :
    ∀ z ∈ rightHalfPlane, g z = 0 := by
  have h_open : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hg_ana : AnalyticOnNhd ℂ g {z : ℂ | 0 < z.re} :=
    h_open.analyticOn_iff_analyticOnNhd.mp (hg_holo.analyticOn h_open)
  have h_conv : Convex ℝ {z : ℂ | 0 < z.re} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq, Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hx hy ⊢
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · simp only [zero_mul, zero_add] at hab ⊢
      rw [hab, one_mul]
      exact hy
    · nlinarith
  let r_seq : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hr_pos : ∀ n : ℕ, 0 < r_seq n := fun n => by dsimp [r_seq]; positivity
  have h_inv_tendsto : Tendsto (fun n : ℕ => (r_seq n : ℂ)) atTop (𝓝 0) := by
    have hr : Tendsto r_seq atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  have h_freq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), g w = 0 := by
    let u : ℕ → ℂ := fun n => (1 : ℂ) + (r_seq n : ℂ)
    have hu_t : Tendsto u atTop (𝓝 (1 : ℂ)) := by
      simpa [u] using tendsto_const_nhds.add h_inv_tendsto
    have hu_ne : ∀ n : ℕ, u n ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
      intro n h1
      rw [Set.mem_singleton_iff] at h1
      have hre := congrArg Complex.re h1
      simp only [u, Complex.add_re, Complex.one_re, Complex.ofReal_re, add_eq_left] at hre
      linarith [hr_pos n]
    have hu_within : Tendsto u atTop (𝓝[≠] (1 : ℂ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hu_t
        (Filter.Eventually.of_forall hu_ne)
    rw [Filter.frequently_iff]
    intro U hU
    rcases (hu_within.eventually hU).exists with ⟨n, hn⟩
    refine ⟨u n, hn, ?_⟩
    have hu_real : u n = ((1 + r_seq n : ℝ) : ℂ) := by dsimp [u]; push_cast; rfl
    rw [hu_real]
    exact hg_real _ (by linarith [hr_pos n])
  have h_open_zero : Set.EqOn g 0 {z : ℂ | 0 < z.re} :=
    hg_ana.eqOn_zero_of_preconnected_of_frequently_eq_zero h_conv.isPreconnected
      (by simp : (1 : ℂ) ∈ {z : ℂ | 0 < z.re}) h_freq
  intro z hz
  let v : ℕ → ℂ := fun n => z + (r_seq n : ℂ)
  have hv_t : Tendsto v atTop (𝓝 z) := by
    simpa [v] using tendsto_const_nhds.add h_inv_tendsto
  have hv_pos : ∀ n : ℕ, 0 < (v n).re := by
    intro n
    have hz_re : 0 ≤ z.re := hz
    simp only [v, Complex.add_re, Complex.ofReal_re]
    linarith [hr_pos n]
  have hv_within : Tendsto v atTop (𝓝[rightHalfPlane] z) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within v hv_t
      (Filter.Eventually.of_forall (fun n => (hv_pos n).le))
  have hg_lim₁ : Tendsto (g ∘ v) atTop (𝓝 (g z)) :=
    (hg_cont.continuousWithinAt hz).tendsto.comp hv_within
  have hg_lim₂ : Tendsto (g ∘ v) atTop (𝓝 0) := by
    have h0 : g ∘ v = fun _ : ℕ => (0 : ℂ) :=
      funext (fun n => h_open_zero (hv_pos n))
    rw [h0]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hg_lim₁ hg_lim₂

lemma fockSemigroup_weaklyHolomorphic {ν : ℕ} (m : ℝ) (χ ψ : FockHilbert ν) :
    ∃ F : ℂ → ℂ,
      (∀ (z : ℂ) (hz : z ∈ rightHalfPlane), F z = ⟪χ, fockSemigroup m z hz ψ⟫_ℂ) ∧
      ContinuousOn F rightHalfPlane ∧
      DifferentiableOn ℂ F {z : ℂ | 0 < z.re} := by
  let g : FockOmega ν → ℂ :=
    fun a => star ((χ : FockOmega ν → ℂ) a) * (ψ : FockOmega ν → ℂ) a
  let dom : FockOmega ν → ℝ :=
    fun a => (‖(χ : FockOmega ν → ℂ) a‖ ^ 2 + ‖(ψ : FockOmega ν → ℂ) a‖ ^ 2) / 2
  have hdom_int : Integrable dom (fockMeasure ν) :=
    ((lp2_integrable_norm_sq χ).add (lp2_integrable_norm_sq ψ)).div_const 2
  have hg_le : ∀ a : FockOmega ν, ‖g a‖ ≤ dom a := by
    intro a
    simp only [g, dom, norm_mul, norm_star]
    nlinarith [sq_nonneg (‖(χ : FockOmega ν → ℂ) a‖ - ‖(ψ : FockOmega ν → ℂ) a‖)]
  have hg_meas : AEStronglyMeasurable g (fockMeasure ν) :=
    (Lp.aestronglyMeasurable χ).star.mul (Lp.aestronglyMeasurable ψ)
  have h_meas_F : ∀ z : ℂ,
      AEStronglyMeasurable
        (fun a : FockOmega ν => laplaceExp (fockEnergy m a) z * g a) (fockMeasure ν) := by
    intro z
    have h_lap : Measurable (fun a : FockOmega ν => laplaceExp (fockEnergy m a) z) :=
      (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).measurable.comp
        (measurable_fockEnergy ν m)
    exact h_lap.aestronglyMeasurable.mul hg_meas
  have h_dom_rhp : ∀ {z : ℂ}, z ∈ rightHalfPlane → ∀ a : FockOmega ν,
      ‖laplaceExp (fockEnergy m a) z * g a‖ ≤ dom a := by
    intro z hz a
    rw [norm_mul]
    calc ‖laplaceExp (fockEnergy m a) z‖ * ‖g a‖
        ≤ 1 * dom a :=
          mul_le_mul (norm_laplaceExp_le_one (fockEnergy_nonneg m a) hz) (hg_le a)
            (norm_nonneg _) zero_le_one
      _ = dom a := one_mul _
  let F : ℂ → ℂ := fun z =>
    ∫ a : FockOmega ν, laplaceExp (fockEnergy m a) z * g a ∂(fockMeasure ν)
  refine ⟨F, fun z hz => (inner_fockSemigroup_eq m z hz χ ψ).symm, ?_, ?_⟩
  · exact MeasureTheory.continuousOn_of_dominated
      (fun z _ => h_meas_F z)
      (fun z hz => Filter.Eventually.of_forall (h_dom_rhp hz))
      hdom_int
      (Filter.Eventually.of_forall (fun a =>
        ((differentiable_laplaceExp (fockEnergy m a)).continuous.mul
          continuous_const).continuousOn))
  · intro z₀ hz₀
    have hz₀_pos : 0 < z₀.re := hz₀
    let r : ℝ := z₀.re / 2
    have hr_pos : 0 < r := half_pos hz₀_pos
    let s : Set ℂ := Metric.ball z₀ r
    have hs_nhds : s ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hr_pos
    have hs_re : ∀ z ∈ s, r ≤ z.re := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have h_abs : |z.re - z₀.re| < r := (Complex.abs_re_le_norm (z - z₀)).trans_lt hz
      have h_low := (abs_lt.mp h_abs).1
      dsimp [r] at h_low ⊢
      linarith
    let F' : ℂ → FockOmega ν → ℂ :=
      fun z a => (-(fockEnergy m a : ℂ) * laplaceExp (fockEnergy m a) z) * g a
    have hF'_meas : AEStronglyMeasurable (F' z₀) (fockMeasure ν) := by
      have hE_c : Measurable (fun a : FockOmega ν => -(fockEnergy m a : ℂ)) :=
        (continuous_neg.comp Complex.continuous_ofReal).measurable.comp
          (measurable_fockEnergy ν m)
      have h_eq' : F' z₀ = fun a => (-(fockEnergy m a : ℂ)) *
          (laplaceExp (fockEnergy m a) z₀ * g a) := by
        ext a
        dsimp [F']
        ring
      rw [h_eq']
      exact hE_c.aestronglyMeasurable.mul (h_meas_F z₀)
    let bound : FockOmega ν → ℝ := fun a => r⁻¹ * dom a
    have h_bound_int : Integrable bound (fockMeasure ν) := hdom_int.const_mul r⁻¹
    have h_bound : ∀ᵐ a : FockOmega ν ∂(fockMeasure ν), ∀ z ∈ s, ‖F' z a‖ ≤ bound a := by
      refine Filter.Eventually.of_forall (fun a z hz => ?_)
      have h_lap_norm : ‖-(fockEnergy m a : ℂ) * laplaceExp (fockEnergy m a) z‖ ≤ r⁻¹ := by
        have h_exp_arg : -z.re * fockEnergy m a = -(fockEnergy m a * z.re) := by ring
        rw [norm_mul, norm_neg, Complex.norm_real,
            Real.norm_of_nonneg (fockEnergy_nonneg m a), norm_laplaceExp, h_exp_arg]
        exact mul_exp_neg_mul_le_inv_of_nonneg (fockEnergy_nonneg m a) hr_pos (hs_re z hz)
      dsimp [F', bound]
      rw [norm_mul]
      exact mul_le_mul h_lap_norm (hg_le a) (norm_nonneg _) (inv_nonneg.mpr hr_pos.le)
    have h_diff : ∀ᵐ a : FockOmega ν ∂(fockMeasure ν), ∀ z ∈ s,
        HasDerivAt (fun w => laplaceExp (fockEnergy m a) w * g a) (F' z a) z := by
      refine Filter.Eventually.of_forall (fun a z _ => ?_)
      have h_lin : HasDerivAt (fun w : ℂ => -w * (fockEnergy m a : ℂ))
          (-1 * (fockEnergy m a : ℂ)) z :=
        (hasDerivAt_id z).neg.mul_const (fockEnergy m a : ℂ)
      have h_mul := h_lin.cexp.mul_const (g a)
      unfold laplaceExp
      exact h_mul.congr_deriv (by dsimp [F', laplaceExp]; ring)
    have hz₀_rhp : z₀ ∈ rightHalfPlane := le_of_lt hz₀_pos
    have hF_z₀_int : Integrable
        (fun a : FockOmega ν => laplaceExp (fockEnergy m a) z₀ * g a) (fockMeasure ν) :=
      hdom_int.mono' (h_meas_F z₀) (Filter.Eventually.of_forall (h_dom_rhp hz₀_rhp))
    have h_deriv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      hs_nhds (Filter.Eventually.of_forall h_meas_F) hF_z₀_int hF'_meas
      h_bound h_bound_int h_diff).2
    exact h_deriv.differentiableAt.differentiableWithinAt

lemma fockSemigroup_mem_closedSubmodule {ν : ℕ} (m : ℝ)
    {K : Submodule ℂ (FockHilbert ν)} (hK_closed : IsClosed (K : Set (FockHilbert ν)))
    (hK_real : ∀ (τ : ℝ) (hτ : 0 ≤ τ) (ψ : FockHilbert ν),
      ψ ∈ K → fockSemigroup m (τ : ℂ) (ofReal_mem_rightHalfPlane hτ) ψ ∈ K)
    (z : ℂ) (hz : z ∈ rightHalfPlane) {ψ : FockHilbert ν} (hψ : ψ ∈ K) :
    fockSemigroup m z hz ψ ∈ K := by
  have hK_ortho : Kᗮᗮ = K := by
    rw [K.orthogonal_orthogonal_eq_closure]
    exact SetLike.ext' hK_closed.closure_eq
  rw [← hK_ortho, Submodule.mem_orthogonal]
  intro χ hχ
  rcases fockSemigroup_weaklyHolomorphic m χ ψ with ⟨F, hF_eq, hF_cont, hF_diff⟩
  rw [← hF_eq z hz]
  refine eq_zero_on_rightHalfPlane_of_real_zero hF_diff hF_cont (fun τ hτ => ?_) z hz
  rw [hF_eq (τ : ℂ) (ofReal_mem_rightHalfPlane hτ)]
  exact Submodule.inner_left_of_mem_orthogonal (hK_real τ hτ ψ hψ) hχ

noncomputable def conjugateSubmoduleCLM {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι_E : E →ₗᵢ[ℂ] H) (T : H →L[ℂ] H)
    (hT : ∀ v ∈ LinearMap.range ι_E.toLinearMap,
      T v ∈ LinearMap.range ι_E.toLinearMap) :
    E →L[ℂ] E :=
  let K : Submodule ℂ H := LinearMap.range ι_E.toLinearMap
  let e : E ≃ₗᵢ[ℂ] K := ι_E.equivRange
  let T_K : K →L[ℂ] K :=
    (LinearMap.codRestrict K (T.toLinearMap.comp K.subtype)
      (fun v => hT v.1 v.2)).mkContinuous ‖T‖
      (fun v => by
        change ‖T v.1‖ ≤ ‖T‖ * ‖v.1‖
        exact T.le_opNorm v.1)
  (e.symm.toContinuousLinearEquiv : K →L[ℂ] E).comp
    (T_K.comp (e.toContinuousLinearEquiv : E →L[ℂ] K))

lemma ι_conjugateSubmoduleCLM {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι_E : E →ₗᵢ[ℂ] H) (T : H →L[ℂ] H)
    (hT : ∀ v ∈ LinearMap.range ι_E.toLinearMap,
      T v ∈ LinearMap.range ι_E.toLinearMap)
    (x : E) :
    ι_E (conjugateSubmoduleCLM ι_E T hT x) = T (ι_E x) := by
  let K : Submodule ℂ H := LinearMap.range ι_E.toLinearMap
  let e : E ≃ₗᵢ[ℂ] K := ι_E.equivRange
  have he_symm : ∀ u : K, ι_E (e.symm u) = u.1 := by
    intro u
    have h1 : (e (e.symm u)).1 = u.1 := congrArg Subtype.val (e.apply_symm_apply u)
    exact h1
  exact he_symm ⟨T (ι_E x), hT (ι_E x) ⟨x, rfl⟩⟩

noncomputable def wickMassShellOSContinuousSpectralData {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (D : OSReflectionPositiveData R_rep S)
    (hD : D.𝒮 = wickMassShellS m hm η C hC)
    (hcontr : OSContractionCondition D) :
    OSContinuousSpectralData D hcontr (FockOmega M_mode.ν) :=
  let h_ker : ∀ A B : OSConfig ι,
      ⟪fockOSMap hm M_mode hC A, fockOSMap hm M_mode hC B⟫_ℂ = osKernel S D.𝒮 A B := by
    intro A B
    rw [hD]
    exact inner_fockOSMap_eq_osKernel hm M_mode hC hC_herm A B
  let ι_OS : OSHilbert D →ₗᵢ[ℂ] FockHilbert M_mode.ν :=
    wavepacketOSLinearIsometry D (fockOSMap hm M_mode hC) h_ker
  let K : Submodule ℂ (FockHilbert M_mode.ν) := LinearMap.range ι_OS.toLinearMap
  have hK_closed : IsClosed (K : Set (FockHilbert M_mode.ν)) :=
    ι_OS.isometry.isUniformInducing.isComplete_range.isClosed
  have h_inter_real : ∀ (τ : ℝ) (hτ : 0 ≤ τ) (x : OSHilbert D),
      ι_OS (osContractionSemigroup D hcontr τ hτ x) =
        fockSemigroup m (τ : ℂ) (ofReal_mem_rightHalfPlane hτ) (ι_OS x) :=
    fun τ hτ x => wavepacketOSLinearIsometry_intertwines_contraction D hcontr
      (fockOSMap hm M_mode hC) h_ker τ hτ
      (fockSemigroup m (τ : ℂ) (ofReal_mem_rightHalfPlane hτ))
      (fockOSMap_osConfigTimeShift hm M_mode hC τ hτ) x
  have hK_inv : ∀ (z : ℂ) (hz : z ∈ rightHalfPlane),
      ∀ v ∈ K, fockSemigroup m z hz v ∈ K := by
    intro z hz v hv
    refine fockSemigroup_mem_closedSubmodule m hK_closed (fun τ hτ ψ hψ => ?_) z hz hv
    rcases hψ with ⟨x, rfl⟩
    exact ⟨osContractionSemigroup D hcontr τ hτ x, h_inter_real τ hτ x⟩
  let Z : ∀ z : ℂ, z ∈ rightHalfPlane → (OSHilbert D →L[ℂ] OSHilbert D) :=
    fun z hz => conjugateSubmoduleCLM ι_OS (fockSemigroup m z hz) (hK_inv z hz)
  have hZ_inter : ∀ (z : ℂ) (hz : z ∈ rightHalfPlane) (x : OSHilbert D),
      ι_OS (Z z hz x) = fockSemigroup m z hz (ι_OS x) :=
    fun z hz x => ι_conjugateSubmoduleCLM ι_OS (fockSemigroup m z hz) (hK_inv z hz) x
  have h_vac : ι_OS (osVacuum D) = fockVacuum M_mode.ν :=
    (wavepacketOSLinearIsometry_osVacuum D (fockOSMap hm M_mode hC) h_ker).trans
      (fockOSMap_osVacuumConfig hm M_mode hC)
  { μ := fockMeasure M_mode.ν
    E := fockEnergy m
    measurable_E := measurable_fockEnergy M_mode.ν m
    energy_nonneg := fockEnergy_nonneg m
    ℰ :=
      { Z := Z
        real_eq := fun τ hτ => by
          ext x
          apply ι_OS.injective
          rw [hZ_inter, h_inter_real]
        map_add := fun z₁ z₂ h₁ h₂ => by
          ext x
          apply ι_OS.injective
          simp only [ContinuousLinearMap.comp_apply, hZ_inter]
          rw [fockSemigroup_add m h₁ h₂, ContinuousLinearMap.comp_apply]
        vacuum := fun z hz => by
          apply ι_OS.injective
          rw [hZ_inter, h_vac, fockSemigroup_fockVacuum]
        contraction := fun z hz x => by
          rw [← ι_OS.norm_map, ← ι_OS.norm_map x, hZ_inter]
          exact norm_fockSemigroup_le m z hz (ι_OS x)
        adjoint_symm := fun z hz x y => by
          rw [← ι_OS.inner_map_map, ← ι_OS.inner_map_map x, hZ_inter, hZ_inter]
          exact fockSemigroup_adjoint_symm m z hz (ι_OS x) (ι_OS y)
        comm_spatial := fun htrans b z hz => by
          have h_sp : ∀ x : OSHilbert D,
              ι_OS (osSpatialTranslate D htrans b x) =
                fockSpatialTranslate m b (ι_OS x) :=
            wavepacketOSLinearIsometry_intertwines_spatial D htrans
              (fockOSMap hm M_mode hC) h_ker b (fockSpatialTranslate m b)
              (fockOSMap_osConfigSpatialShift hm M_mode hC b)
          ext x
          apply ι_OS.injective
          have hc := congrArg (fun T => T (ι_OS x))
            (fockSpatialTranslate_comm_fockSemigroup (ν := M_mode.ν) m b z hz)
          simp only [ContinuousLinearMap.comp_apply] at hc ⊢
          rw [h_sp, hZ_inter, hc, ← h_sp, ← hZ_inter] }
    wave := fun x => (ι_OS x : FockOmega M_mode.ν → ℂ)
    aestronglyMeasurable_wave := fun x => Lp.aestronglyMeasurable (ι_OS x)
    integrable_norm_sq := fun x => lp2_integrable_norm_sq (ι_OS x)
    norm_sq_eq_integral := fun x => by
      rw [← ι_OS.norm_map x]
      exact lp2_norm_sq_eq_integral (ι_OS x)
    semigroup_inner_eq := fun z hz x y => by
      rw [← ι_OS.inner_map_map, hZ_inter]
      exact inner_fockSemigroup_eq m z hz (ι_OS x) (ι_OS y) }

noncomputable def freeKGOSContinuousSpectralData {m : ℝ} (hm : 0 < m) :
    OSContinuousSpectralData (freeKGOSAxioms hm).toReflectionPositiveData
      (osContractionCondition_of_timeCluster (freeKGOSAxioms hm).toReflectionPositiveData
        (freeKGOSAxioms hm).os1_translation (freeKGOSTimeCluster hm))
      (FockOmega (kgModeData hm).ν) :=
  wickMassShellOSContinuousSpectralData hm (kgModeData hm) (massiveKGCoeff_data hm)
    (fun _ _ => by simp [massiveKGCoeff, trivialStarStructure]) _ rfl _

noncomputable def freeDiracOSContinuousSpectralData {m : ℝ} (hm : 0 < m) :
    OSContinuousSpectralData (freeDiracOSAxioms hm).toReflectionPositiveData
      (osContractionCondition_of_timeCluster (freeDiracOSAxioms hm).toReflectionPositiveData
        (freeDiracOSAxioms hm).os1_translation (freeDiracOSTimeCluster hm))
      (FockOmega (diracModeData hm).ν) :=
  wickMassShellOSContinuousSpectralData hm (diracModeData hm) (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_herm m) _ rfl _

noncomputable def freeKGOSHolomorphicSemigroup {m : ℝ} (hm : 0 < m) :
    OSHolomorphicSemigroup (freeKGOSAxioms hm).toReflectionPositiveData
      (osContractionCondition_of_timeCluster (freeKGOSAxioms hm).toReflectionPositiveData
        (freeKGOSAxioms hm).os1_translation (freeKGOSTimeCluster hm)) :=
  (freeKGOSContinuousSpectralData hm).ℰ

theorem freeKGOSHolomorphicSemigroup_isWeaklyHolomorphic {m : ℝ} (hm : 0 < m) :
    (freeKGOSHolomorphicSemigroup hm).IsWeaklyHolomorphic :=
  (freeKGOSContinuousSpectralData hm).isWeaklyHolomorphic

noncomputable def freeDiracOSHolomorphicSemigroup {m : ℝ} (hm : 0 < m) :
    OSHolomorphicSemigroup (freeDiracOSAxioms hm).toReflectionPositiveData
      (osContractionCondition_of_timeCluster (freeDiracOSAxioms hm).toReflectionPositiveData
        (freeDiracOSAxioms hm).os1_translation (freeDiracOSTimeCluster hm)) :=
  (freeDiracOSContinuousSpectralData hm).ℰ

theorem freeDiracOSHolomorphicSemigroup_isWeaklyHolomorphic {m : ℝ} (hm : 0 < m) :
    (freeDiracOSHolomorphicSemigroup hm).IsWeaklyHolomorphic :=
  (freeDiracOSContinuousSpectralData hm).isWeaklyHolomorphic

lemma tendsto_integral_exp_I_mul_atTop (f : ℝ → ℂ) :
    Tendsto (fun t : ℝ => ∫ s : ℝ, f s * Complex.exp (Complex.I * (t : ℂ) * (s : ℂ)))
      atTop (𝓝 0) := by
  have hc : Tendsto (fun t : ℝ => -(t / (2 * Real.pi))) atTop (cocompact ℝ) := by
    refine tendsto_cocompact_of_tendsto_dist_comp_atTop (0 : ℝ) ?_
    have h_pos : (0 : ℝ) < (2 * Real.pi)⁻¹ := inv_pos.mpr (by positivity)
    have h_lin : Tendsto (fun t : ℝ => (2 * Real.pi)⁻¹ * t) atTop atTop :=
      Filter.Tendsto.const_mul_atTop h_pos tendsto_id
    refine tendsto_atTop_mono (fun t => ?_) h_lin
    rw [Real.dist_eq, sub_zero, abs_neg, abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi),
        div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (le_abs_self t) h_pos.le
  have h_rl := (Real.tendsto_integral_exp_smul_cocompact f).comp hc
  refine h_rl.congr (fun t => ?_)
  dsimp only [Function.comp_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
  dsimp only
  rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  have h_arg : (((2 * Real.pi * -(s * -(t / (2 * Real.pi))) : ℝ) : ℂ) * Complex.I) =
      Complex.I * (t : ℂ) * (s : ℂ) := by
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    field_simp [hpi]
  rw [h_arg, mul_comm]

lemma tendsto_setIntegral_oscillatory_of_injOn
    {S : Set ℝ} (hS : MeasurableSet S)
    {φ φ' : ℝ → ℝ} (hφ' : ∀ s ∈ S, HasDerivWithinAt φ (φ' s) S s)
    (h_inj : Set.InjOn φ S) (h_ne : ∀ s ∈ S, φ' s ≠ 0)
    (h_img : MeasurableSet (φ '' S)) (g : ℝ → ℂ) :
    Tendsto (fun t : ℝ =>
      ∫ s in S, g s * Complex.exp (Complex.I * (t : ℂ) * (φ s : ℂ)))
      atTop (𝓝 0) := by
  let H : ℝ → ℂ := Set.indicator (φ '' S)
    (fun u => (|φ' (Function.invFunOn φ S u)|)⁻¹ • g (Function.invFunOn φ S u))
  have h_eq : ∀ t : ℝ,
      (∫ u : ℝ, H u * Complex.exp (Complex.I * (t : ℂ) * (u : ℂ))) =
        ∫ s in S, g s * Complex.exp (Complex.I * (t : ℂ) * (φ s : ℂ)) := by
    intro t
    let Kt : ℝ → ℂ := fun u => H u * Complex.exp (Complex.I * (t : ℂ) * (u : ℂ))
    have h_ind : Kt = Set.indicator (φ '' S) Kt := by
      ext u
      by_cases hu : u ∈ φ '' S
      · simp [hu]
      · simp [Kt, H, hu]
    change (∫ u : ℝ, Kt u) = _
    rw [h_ind, integral_indicator h_img,
        integral_image_eq_integral_abs_deriv_smul hS hφ' h_inj Kt]
    refine setIntegral_congr_fun hS (fun s hs => ?_)
    dsimp only [Kt, H]
    have hmem : φ s ∈ φ '' S := Set.mem_image_of_mem φ hs
    have hinv : Function.invFunOn φ S (φ s) = s := h_inj.leftInvOn_invFunOn hs
    have habs : |φ' s| ≠ 0 := abs_ne_zero.mpr (h_ne s hs)
    rw [Set.indicator_of_mem hmem, hinv, Complex.real_smul, Complex.real_smul,
        ← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ habs,
        Complex.ofReal_one, one_mul]
  exact (tendsto_integral_exp_I_mul_atTop H).congr h_eq

lemma tendsto_setIntegral_oscillatory_of_hasDerivAt_sign
    {S : Set ℝ} (hS_meas : MeasurableSet S) (hS_conv : Convex ℝ S)
    {φ φ' : ℝ → ℝ} (hφ : ∀ s : ℝ, HasDerivAt φ (φ' s) s)
    (h_sign : (∀ s ∈ S, 0 < φ' s) ∨ (∀ s ∈ S, φ' s < 0))
    (g : ℝ → ℂ) :
    Tendsto (fun t : ℝ =>
      ∫ s in S, g s * Complex.exp (Complex.I * (t : ℂ) * (φ s : ℂ)))
      atTop (𝓝 0) := by
  have hφ_cont : Continuous φ :=
    Differentiable.continuous (𝕜 := ℝ) (fun s => (hφ s).differentiableAt)
  have hφ_within : ∀ s ∈ S, HasDerivWithinAt φ (φ' s) S s :=
    fun s _ => (hφ s).hasDerivWithinAt
  rcases h_sign with h_pos | h_neg
  · have h_sm : StrictMonoOn φ S :=
      strictMonoOn_of_deriv_pos hS_conv hφ_cont.continuousOn
        (fun s hs => by rw [(hφ s).deriv]; exact h_pos s (interior_subset hs))
    exact tendsto_setIntegral_oscillatory_of_injOn hS_meas hφ_within h_sm.injOn
      (fun s hs => (h_pos s hs).ne') (hS_meas.image_of_monotoneOn h_sm.monotoneOn) g
  · have h_sa : StrictAntiOn φ S :=
      strictAntiOn_of_deriv_neg hS_conv hφ_cont.continuousOn
        (fun s hs => by rw [(hφ s).deriv]; exact h_neg s (interior_subset hs))
    exact tendsto_setIntegral_oscillatory_of_injOn hS_meas hφ_within h_sa.injOn
      (fun s hs => (h_neg s hs).ne) (hS_meas.image_of_antitoneOn h_sa.antitoneOn) g

noncomputable def hyperboloidVel (M s : ℝ) : ℝ :=
  s / Real.sqrt (M ^ 2 + s ^ 2)

lemma abs_hyperboloidVel_lt_one {M : ℝ} (hM : 0 < M) (s : ℝ) :
    |hyperboloidVel M s| < 1 := by
  have hden : 0 < Real.sqrt (M ^ 2 + s ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have h_lt : |s| < Real.sqrt (M ^ 2 + s ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg s) (by nlinarith [mul_self_pos.mpr hM.ne'])
  unfold hyperboloidVel
  rw [abs_div, abs_of_pos hden, div_lt_one hden]
  exact h_lt

lemma hasDerivAt_sqrt_sq_add_sq {M : ℝ} (hM : 0 < M) (s : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sqrt (M ^ 2 + x ^ 2)) (hyperboloidVel M s) s := by
  have h_pos : M ^ 2 + s ^ 2 ≠ 0 := by positivity
  have h_quad : HasDerivAt (fun x : ℝ => M ^ 2 + x ^ 2) (2 * s) s := by
    simpa using ((hasDerivAt_pow 2 s).const_add (M ^ 2))
  refine (h_quad.sqrt h_pos).congr_deriv ?_
  unfold hyperboloidVel
  have h_sqrt_ne : Real.sqrt (M ^ 2 + s ^ 2) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by positivity)
  field_simp [h_sqrt_ne]

lemma strictMono_hyperboloidVel {M : ℝ} (hM : 0 < M) :
    StrictMono (hyperboloidVel M) := by
  have h_deriv : ∀ s : ℝ,
      HasDerivAt (hyperboloidVel M)
        (M ^ 2 / (Real.sqrt (M ^ 2 + s ^ 2) * (M ^ 2 + s ^ 2))) s := by
    intro s
    have h_pos : 0 < M ^ 2 + s ^ 2 := by positivity
    have h_sqrt_pos : 0 < Real.sqrt (M ^ 2 + s ^ 2) := Real.sqrt_pos.mpr h_pos
    have h_q := (hasDerivAt_id s).div (hasDerivAt_sqrt_sq_add_sq hM s) h_sqrt_pos.ne'
    refine h_q.congr_deriv ?_
    unfold hyperboloidVel
    dsimp only [id_eq]
    have h_sq : Real.sqrt (M ^ 2 + s ^ 2) ^ 2 = M ^ 2 + s ^ 2 := Real.sq_sqrt h_pos.le
    rw [h_sq]
    field_simp [h_sqrt_pos.ne', h_pos.ne']
    rw [h_sq]
    ring
  refine strictMono_of_deriv_pos (fun s => ?_)
  rw [(h_deriv s).deriv]
  have h_pos : 0 < M ^ 2 + s ^ 2 := by positivity
  have h_sqrt_pos : 0 < Real.sqrt (M ^ 2 + s ^ 2) := Real.sqrt_pos.mpr h_pos
  positivity

lemma tendsto_hyperboloid_oscillatory {M : ℝ} (hM : 0 < M)
    {a₀ a₁ : ℝ} (ha₀ : a₀ ≠ 0) (c₀ : ℝ)
    {g : ℝ → ℂ} (hg : Integrable g volume) :
    Tendsto (fun t : ℝ =>
      ∫ s : ℝ, g s * Complex.exp (Complex.I * (t : ℂ) *
        ((a₀ * Real.sqrt (M ^ 2 + s ^ 2) - a₁ * s + c₀ : ℝ) : ℂ)))
      atTop (𝓝 0) := by
  let φ : ℝ → ℝ := fun s => a₀ * Real.sqrt (M ^ 2 + s ^ 2) - a₁ * s + c₀
  let φ' : ℝ → ℝ := fun s => a₀ * hyperboloidVel M s - a₁
  have hφ : ∀ s : ℝ, HasDerivAt φ (φ' s) s := by
    intro s
    have h1 := (hasDerivAt_sqrt_sq_add_sq hM s).const_mul a₀
    have h2 : HasDerivAt (fun x : ℝ => a₁ * x) a₁ s := by
      simpa using (hasDerivAt_id s).const_mul a₁
    simpa [φ, φ'] using (h1.sub h2).add_const c₀
  change Tendsto (fun t : ℝ =>
    ∫ s : ℝ, g s * Complex.exp (Complex.I * (t : ℂ) * (φ s : ℂ))) atTop (𝓝 0)
  by_cases h_cmp : |a₀| ≤ |a₁|
  · have h_univ : ∀ t : ℝ,
        (∫ s : ℝ, g s * Complex.exp (Complex.I * (t : ℂ) * (φ s : ℂ))) =
          ∫ s in Set.univ, g s * Complex.exp (Complex.I * (t : ℂ) * (φ s : ℂ)) :=
      fun _ => Measure.restrict_univ.symm ▸ rfl
    rw [funext h_univ]
    refine tendsto_setIntegral_oscillatory_of_hasDerivAt_sign
      MeasurableSet.univ convex_univ hφ ?_ g
    have h_abs_lt : ∀ s : ℝ, |a₀ * hyperboloidVel M s| < |a₁| := by
      intro s
      rw [abs_mul]
      have hv := abs_hyperboloidVel_lt_one hM s
      have ha₀_pos : 0 < |a₀| := abs_pos.mpr ha₀
      exact (mul_lt_of_lt_one_right ha₀_pos hv).trans_le h_cmp
    by_cases ha₁_nn : 0 ≤ a₁
    · refine Or.inr (fun s _ => ?_)
      have h_lt := (abs_lt.mp (h_abs_lt s)).2
      rw [abs_of_nonneg ha₁_nn] at h_lt
      dsimp [φ']
      linarith
    · refine Or.inl (fun s _ => ?_)
      have ha₁_neg : a₁ < 0 := not_le.mp ha₁_nn
      have h_lt := (abs_lt.mp (h_abs_lt s)).1
      rw [abs_of_neg ha₁_neg] at h_lt
      dsimp [φ']
      linarith
  · have h_cmp_lt : |a₁| < |a₀| := not_le.mp h_cmp
    let r : ℝ := a₁ / a₀
    have hr_abs : |r| < 1 := by
      dsimp [r]
      rw [abs_div, div_lt_one (abs_pos.mpr ha₀)]
      exact h_cmp_lt
    have hr_sq : 0 < 1 - r ^ 2 := by
      have hsq : r ^ 2 < 1 ^ 2 := sq_lt_sq.mpr (by simpa using hr_abs)
      linarith
    let s₀ : ℝ := r * M / Real.sqrt (1 - r ^ 2)
    have hv_s₀ : hyperboloidVel M s₀ = r := by
      have h_root_pos : 0 < Real.sqrt (1 - r ^ 2) := Real.sqrt_pos.mpr hr_sq
      have h_sum_sq : M ^ 2 + s₀ ^ 2 = M ^ 2 / (1 - r ^ 2) := by
        dsimp [s₀]
        rw [div_pow, mul_pow, Real.sq_sqrt hr_sq.le]
        field_simp [hr_sq.ne']
        ring
      unfold hyperboloidVel
      rw [h_sum_sq, Real.sqrt_div (sq_nonneg M), Real.sqrt_sq hM.le]
      dsimp [s₀]
      field_simp [hM.ne', h_root_pos.ne']
    have hφ'_eq : ∀ s : ℝ, φ' s = a₀ * (hyperboloidVel M s - hyperboloidVel M s₀) := by
      intro s
      dsimp [φ']
      rw [hv_s₀]
      dsimp [r]
      field_simp [ha₀]
    have h_split : ∀ t : ℝ,
        (∫ s : ℝ, g s * Complex.exp (Complex.I * (t : ℂ) * (φ s : ℂ))) =
          (∫ s in Set.Iio s₀, g s * Complex.exp (Complex.I * (t : ℂ) * (φ s : ℂ))) +
            (∫ s in Set.Ioi s₀, g s * Complex.exp (Complex.I * (t : ℂ) * (φ s : ℂ))) := by
      intro t
      let F_t : ℝ → ℂ := fun s => g s * Complex.exp (Complex.I * (t : ℂ) * (φ s : ℂ))
      have hF_int : Integrable F_t volume := by
        have h_meas : Measurable (fun s : ℝ =>
            Complex.exp (Complex.I * (t : ℂ) * (φ s : ℂ))) := by
          have hφ_cont : Continuous φ :=
            Differentiable.continuous (𝕜 := ℝ) (fun s => (hφ s).differentiableAt)
          exact Complex.continuous_exp.measurable.comp
            (measurable_const.mul (Complex.continuous_ofReal.measurable.comp hφ_cont.measurable))
        refine hg.norm.mono' (hg.1.mul h_meas.aestronglyMeasurable)
          (Filter.Eventually.of_forall (fun s => ?_))
        dsimp [F_t]
        rw [norm_mul]
        have h_exp_norm : ‖Complex.exp (Complex.I * (t : ℂ) * (φ s : ℂ))‖ = 1 := by
          have h_im : Complex.I * (t : ℂ) * (φ s : ℂ) = ((t * φ s : ℝ) : ℂ) * Complex.I := by
            push_cast
            ring
          rw [h_im, Complex.norm_exp_ofReal_mul_I]
        rw [h_exp_norm, mul_one]
      have h_union1 : Set.Iio s₀ ∪ Set.Ici s₀ = Set.univ := Set.Iio_union_Ici
      have h_disj1 : Disjoint (Set.Iio s₀) (Set.Ici s₀) :=
        Set.disjoint_left.mpr (fun _ hx₁ hx₂ =>
          not_le_of_gt (Set.mem_Iio.mp hx₁) (Set.mem_Ici.mp hx₂))
      have h_union2 : ({s₀} : Set ℝ) ∪ Set.Ioi s₀ = Set.Ici s₀ := by
        ext x
        simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_Ioi, Set.mem_Ici]
        rw [eq_comm]
        exact le_iff_eq_or_lt.symm
      have h_disj2 : Disjoint ({s₀} : Set ℝ) (Set.Ioi s₀) :=
        Set.disjoint_singleton_left.mpr (Set.notMem_Ioi.mpr le_rfl)
      have h_sing : (∫ s in ({s₀} : Set ℝ), F_t s) = 0 := by
        rw [Measure.restrict_eq_zero.mpr (measure_singleton s₀), integral_zero_measure]
      change (∫ s : ℝ, F_t s) = (∫ s in Set.Iio s₀, F_t s) + (∫ s in Set.Ioi s₀, F_t s)
      have h_lhs : (∫ s : ℝ, F_t s) = ∫ s in Set.univ, F_t s :=
        Measure.restrict_univ.symm ▸ rfl
      rw [h_lhs, ← h_union1,
          setIntegral_union h_disj1 measurableSet_Ici hF_int.integrableOn hF_int.integrableOn,
          ← h_union2,
          setIntegral_union h_disj2 measurableSet_Ioi hF_int.integrableOn hF_int.integrableOn,
          h_sing, zero_add]
    rw [funext h_split]
    have h_left : Tendsto (fun t : ℝ =>
        ∫ s in Set.Iio s₀, g s * Complex.exp (Complex.I * (t : ℂ) * (φ s : ℂ)))
        atTop (𝓝 0) := by
      refine tendsto_setIntegral_oscillatory_of_hasDerivAt_sign
        measurableSet_Iio (convex_Iio s₀) hφ ?_ g
      rcases lt_or_gt_of_ne ha₀ with ha_neg | ha_pos
      · refine Or.inl (fun s hs => ?_)
        rw [hφ'_eq s]
        exact mul_pos_of_neg_of_neg ha_neg (sub_neg.mpr (strictMono_hyperboloidVel hM hs))
      · refine Or.inr (fun s hs => ?_)
        rw [hφ'_eq s]
        exact mul_neg_of_pos_of_neg ha_pos (sub_neg.mpr (strictMono_hyperboloidVel hM hs))
    have h_right : Tendsto (fun t : ℝ =>
        ∫ s in Set.Ioi s₀, g s * Complex.exp (Complex.I * (t : ℂ) * (φ s : ℂ)))
        atTop (𝓝 0) := by
      refine tendsto_setIntegral_oscillatory_of_hasDerivAt_sign
        measurableSet_Ioi (convex_Ioi s₀) hφ ?_ g
      rcases lt_or_gt_of_ne ha₀ with ha_neg | ha_pos
      · refine Or.inr (fun s hs => ?_)
        rw [hφ'_eq s]
        exact mul_neg_of_neg_of_pos ha_neg (sub_pos.mpr (strictMono_hyperboloidVel hM hs))
      · refine Or.inl (fun s hs => ?_)
        rw [hφ'_eq s]
        exact mul_pos ha_pos (sub_pos.mpr (strictMono_hyperboloidVel hM hs))
    simpa using h_left.add h_right

theorem tendsto_massShell_oscillatory {m : ℝ} (hm : 0 < m)
    {a : Fin 4 → ℝ} (ha : a ≠ 0)
    {G : (Fin 3 → ℝ) → ℂ} (hG : Integrable G volume) :
    Tendsto (fun t : ℝ =>
      ∫ q : Fin 3 → ℝ,
        G q * Complex.exp (Complex.I * (t : ℂ) * (minkowskiInner (massShellVec m q) a : ℂ)))
      atTop (𝓝 0) := by
  by_cases ha0 : a 0 = 0
  · have hex : ∃ j : Fin 3, a j.succ ≠ 0 := by
      by_contra h_all
      apply ha
      ext μ
      refine Fin.cases ha0 (fun j => not_ne_iff.mp (fun hj => h_all ⟨j, hj⟩)) μ
    rcases hex with ⟨j, hj⟩
    let mp := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) j).symm
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) j).symm
    have hG_prod : Integrable (fun sq : ℝ × (Fin 2 → ℝ) => G (e sq)) (volume.prod volume) :=
      (mp.integrable_comp_emb e.measurableEmbedding).mpr hG
    have h_int_prod : ∀ t : ℝ, Integrable
        (fun sq : ℝ × (Fin 2 → ℝ) => G (e sq) * Complex.exp (Complex.I * (t : ℂ) *
          (minkowskiInner (massShellVec m (e sq)) a : ℂ)))
        (volume.prod volume) := by
      intro t
      have h_cont : Continuous (fun q : Fin 3 → ℝ =>
          Complex.exp (Complex.I * (t : ℂ) *
            (minkowskiInner (massShellVec m q) a : ℂ))) := by
        have h_in : Continuous (fun q : Fin 3 → ℝ => minkowskiInner (massShellVec m q) a) := by
          simp only [minkowskiInner_explicit]
          have hc : ∀ μ : Fin 4, Continuous (fun q : Fin 3 → ℝ => massShellVec m q μ) :=
            fun μ => (continuous_apply μ).comp (continuous_massShellVec m)
          exact (((hc 0).mul continuous_const).sub ((hc 1).mul continuous_const)).sub
            ((hc 2).mul continuous_const) |>.sub ((hc 3).mul continuous_const)
        exact Complex.continuous_exp.comp
          (continuous_const.mul (Complex.continuous_ofReal.comp h_in))
      refine hG_prod.norm.mono'
        (hG_prod.1.mul (h_cont.measurable.comp e.measurable).aestronglyMeasurable)
        (Filter.Eventually.of_forall (fun sq => ?_))
      rw [norm_mul]
      have h_en : ‖Complex.exp (Complex.I * (t : ℂ) *
          (minkowskiInner (massShellVec m (e sq)) a : ℂ))‖ = 1 := by
        have h_im : Complex.I * (t : ℂ) * (minkowskiInner (massShellVec m (e sq)) a : ℂ) =
            ((t * minkowskiInner (massShellVec m (e sq)) a : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        rw [h_im, Complex.norm_exp_ofReal_mul_I]
      rw [h_en, mul_one]
    have h_fub : ∀ t : ℝ,
        (∫ q : Fin 3 → ℝ,
          G q * Complex.exp (Complex.I * (t : ℂ) *
            (minkowskiInner (massShellVec m q) a : ℂ))) =
        ∫ q' : Fin 2 → ℝ,
          (∫ s : ℝ, G (e (s, q')) * Complex.exp (Complex.I * (t : ℂ) *
            (minkowskiInner (massShellVec m (e (s, q'))) a : ℂ))) := by
      intro t
      rw [← mp.integral_comp']
      exact integral_prod_symm _ (h_int_prod t)
    rw [funext h_fub]
    have h_dom_int : Integrable
        (fun q' : Fin 2 → ℝ => ∫ s : ℝ, ‖G (e (s, q'))‖) volume :=
      hG_prod.norm.integral_prod_right
    have h0_int : (0 : ℂ) = ∫ _ : Fin 2 → ℝ, (0 : ℂ) := by simp
    rw [h0_int]
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun q' => ∫ s : ℝ, ‖G (e (s, q'))‖) ?_ ?_ h_dom_int ?_
    · exact Filter.Eventually.of_forall (fun t => (h_int_prod t).integral_prod_right.1)
    · refine Filter.Eventually.of_forall (fun t => Filter.Eventually.of_forall (fun q' => ?_))
      refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
        (Filter.Eventually.of_forall (fun s => ?_))))
      dsimp only
      rw [norm_mul]
      have h_en : ‖Complex.exp (Complex.I * (t : ℂ) *
          (minkowskiInner (massShellVec m (e (s, q'))) a : ℂ))‖ = 1 := by
        have h_im : Complex.I * (t : ℂ) *
            (minkowskiInner (massShellVec m (e (s, q'))) a : ℂ) =
            ((t * minkowskiInner (massShellVec m (e (s, q'))) a : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        rw [h_im, Complex.norm_exp_ofReal_mul_I]
      rw [h_en, mul_one]
    · refine Filter.Eventually.of_forall (fun q' => ?_)
      have h_lin_phase : ∃ c₀ : ℝ, ∀ s : ℝ,
          minkowskiInner (massShellVec m (e (s, q'))) a = -(a j.succ) * s + c₀ := by
        fin_cases j
        · refine ⟨-(q' 0 * a 2 + q' 1 * a 3), fun s => ?_⟩
          have he0 : e (s, q') 0 = s := by simp [e]
          have he1 : e (s, q') 1 = q' 0 := by simp [e]
          have he2 : e (s, q') 2 = q' 1 := by
            suffices h : @Fin.cons 2 (fun _ => ℝ) s q' 2 = q' 1 by simpa [e] using h
            rw [← Fin.succ_one_eq_two, Fin.cons_succ]
          simp [minkowskiInner_explicit, massShellVec, ha0, he0, he1, he2]
          ring
        · refine ⟨-(q' 0 * a 1 + q' 1 * a 3), fun s => ?_⟩
          have hi0 : Fin.insertNth (α := fun _ : Fin 3 => ℝ) 1 s q' 0 = q' 0 := rfl
          have hi2 : Fin.insertNth (α := fun _ : Fin 3 => ℝ) 1 s q' 2 = q' 1 := rfl
          simp [e, minkowskiInner_explicit, massShellVec, ha0, hi0, hi2]
          ring
        · refine ⟨-(q' 0 * a 1 + q' 1 * a 2), fun s => ?_⟩
          have hi0 : Fin.insertNth (α := fun _ : Fin 3 => ℝ) 2 s q' 0 = q' 0 := rfl
          have hi1 : Fin.insertNth (α := fun _ : Fin 3 => ℝ) 2 s q' 1 = q' 1 := rfl
          simp [e, minkowskiInner_explicit, massShellVec, ha0, hi0, hi1]
          ring
      rcases h_lin_phase with ⟨c₀, hc₀⟩
      have h_univ : ∀ t : ℝ,
          (∫ s : ℝ, G (e (s, q')) * Complex.exp (Complex.I * (t : ℂ) *
            (minkowskiInner (massShellVec m (e (s, q'))) a : ℂ))) =
          ∫ s in Set.univ, G (e (s, q')) * Complex.exp (Complex.I * (t : ℂ) *
            ((-(a j.succ) * s + c₀ : ℝ) : ℂ)) := by
        intro t
        rw [Measure.restrict_univ]
        exact integral_congr_ae (Filter.Eventually.of_forall (fun s => by dsimp only; rw [hc₀ s]))
      rw [funext h_univ]
      have h_deriv : ∀ s : ℝ, HasDerivAt (fun x : ℝ => -(a j.succ) * x + c₀) (-(a j.succ)) s := by
        intro s
        simpa using ((hasDerivAt_id s).const_mul (-(a j.succ))).add_const c₀
      refine tendsto_setIntegral_oscillatory_of_hasDerivAt_sign
        MeasurableSet.univ convex_univ h_deriv ?_ (fun s => G (e (s, q')))
      rcases lt_or_gt_of_ne (neg_ne_zero.mpr hj) with hneg | hpos
      · exact Or.inr (fun _ _ => hneg)
      · exact Or.inl (fun _ _ => hpos)
  · let mp := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm
    have hG_prod : Integrable (fun sq : ℝ × (Fin 2 → ℝ) => G (e sq)) (volume.prod volume) :=
      (mp.integrable_comp_emb e.measurableEmbedding).mpr hG
    have h_int_prod : ∀ t : ℝ, Integrable
        (fun sq : ℝ × (Fin 2 → ℝ) => G (e sq) * Complex.exp (Complex.I * (t : ℂ) *
          (minkowskiInner (massShellVec m (e sq)) a : ℂ)))
        (volume.prod volume) := by
      intro t
      have h_cont : Continuous (fun q : Fin 3 → ℝ =>
          Complex.exp (Complex.I * (t : ℂ) *
            (minkowskiInner (massShellVec m q) a : ℂ))) := by
        have h_in : Continuous (fun q : Fin 3 → ℝ => minkowskiInner (massShellVec m q) a) := by
          simp only [minkowskiInner_explicit]
          have hc : ∀ μ : Fin 4, Continuous (fun q : Fin 3 → ℝ => massShellVec m q μ) :=
            fun μ => (continuous_apply μ).comp (continuous_massShellVec m)
          exact (((hc 0).mul continuous_const).sub ((hc 1).mul continuous_const)).sub
            ((hc 2).mul continuous_const) |>.sub ((hc 3).mul continuous_const)
        exact Complex.continuous_exp.comp
          (continuous_const.mul (Complex.continuous_ofReal.comp h_in))
      refine hG_prod.norm.mono'
        (hG_prod.1.mul (h_cont.measurable.comp e.measurable).aestronglyMeasurable)
        (Filter.Eventually.of_forall (fun sq => ?_))
      rw [norm_mul]
      have h_en : ‖Complex.exp (Complex.I * (t : ℂ) *
          (minkowskiInner (massShellVec m (e sq)) a : ℂ))‖ = 1 := by
        have h_im : Complex.I * (t : ℂ) * (minkowskiInner (massShellVec m (e sq)) a : ℂ) =
            ((t * minkowskiInner (massShellVec m (e sq)) a : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        rw [h_im, Complex.norm_exp_ofReal_mul_I]
      rw [h_en, mul_one]
    have h_fub : ∀ t : ℝ,
        (∫ q : Fin 3 → ℝ,
          G q * Complex.exp (Complex.I * (t : ℂ) *
            (minkowskiInner (massShellVec m q) a : ℂ))) =
        ∫ q' : Fin 2 → ℝ,
          (∫ s : ℝ, G (e (s, q')) * Complex.exp (Complex.I * (t : ℂ) *
            (minkowskiInner (massShellVec m (e (s, q'))) a : ℂ))) := by
      intro t
      rw [← mp.integral_comp']
      exact integral_prod_symm _ (h_int_prod t)
    rw [funext h_fub]
    have h_dom_int : Integrable
        (fun q' : Fin 2 → ℝ => ∫ s : ℝ, ‖G (e (s, q'))‖) volume :=
      hG_prod.norm.integral_prod_right
    have h_ae_int : ∀ᵐ q' : Fin 2 → ℝ ∂volume,
        Integrable (fun s : ℝ => G (e (s, q'))) volume :=
      (integrable_prod_iff' hG_prod.1).mp hG_prod |>.1
    have h0_int : (0 : ℂ) = ∫ _ : Fin 2 → ℝ, (0 : ℂ) := by simp
    rw [h0_int]
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun q' => ∫ s : ℝ, ‖G (e (s, q'))‖) ?_ ?_ h_dom_int ?_
    · exact Filter.Eventually.of_forall (fun t => (h_int_prod t).integral_prod_right.1)
    · refine Filter.Eventually.of_forall (fun t => Filter.Eventually.of_forall (fun q' => ?_))
      refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
        (Filter.Eventually.of_forall (fun s => ?_))))
      dsimp only
      rw [norm_mul]
      have h_en : ‖Complex.exp (Complex.I * (t : ℂ) *
          (minkowskiInner (massShellVec m (e (s, q'))) a : ℂ))‖ = 1 := by
        have h_im : Complex.I * (t : ℂ) *
            (minkowskiInner (massShellVec m (e (s, q'))) a : ℂ) =
            ((t * minkowskiInner (massShellVec m (e (s, q'))) a : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        rw [h_im, Complex.norm_exp_ofReal_mul_I]
      rw [h_en, mul_one]
    · filter_upwards [h_ae_int] with q' hGq'
      let M : ℝ := Real.sqrt (m ^ 2 + (q' 0) ^ 2 + (q' 1) ^ 2)
      have hM_pos : 0 < M := Real.sqrt_pos.mpr (by positivity)
      let c₀ : ℝ := -(q' 0 * a 2 + q' 1 * a 3)
      have h_phase : ∀ s : ℝ,
          minkowskiInner (massShellVec m (e (s, q'))) a =
            a 0 * Real.sqrt (M ^ 2 + s ^ 2) - a 1 * s + c₀ := by
        intro s
        have hM_sq : M ^ 2 = m ^ 2 + (q' 0) ^ 2 + (q' 1) ^ 2 :=
          Real.sq_sqrt (by positivity)
        have he0 : e (s, q') 0 = s := by simp [e]
        have he1 : e (s, q') 1 = q' 0 := by simp [e]
        have he2 : e (s, q') 2 = q' 1 := by
          suffices h : @Fin.cons 2 (fun _ => ℝ) s q' 2 = q' 1 by simpa [e] using h
          rw [← Fin.succ_one_eq_two, Fin.cons_succ]
        have h_en_eq : massShellEnergy m (e (s, q')) = Real.sqrt (M ^ 2 + s ^ 2) := by
          unfold massShellEnergy massShellSpatialSq
          rw [he0, he1, he2]
          congr 1
          rw [hM_sq]
          ring
        simp [minkowskiInner_explicit, massShellVec, he0, he1, he2, h_en_eq]
        dsimp [c₀]
        ring
      have h_phase_int : ∀ t : ℝ,
          (∫ s : ℝ, G (e (s, q')) * Complex.exp (Complex.I * (t : ℂ) *
            (minkowskiInner (massShellVec m (e (s, q'))) a : ℂ))) =
          ∫ s : ℝ, G (e (s, q')) * Complex.exp (Complex.I * (t : ℂ) *
            ((a 0 * Real.sqrt (M ^ 2 + s ^ 2) - a 1 * s + c₀ : ℝ) : ℂ)) :=
        fun _ => integral_congr_ae (Filter.Eventually.of_forall (fun s => by
          dsimp only; rw [h_phase s]))
      rw [funext h_phase_int]
      exact tendsto_hyperboloid_oscillatory hM_pos ha0 c₀ hGq'

noncomputable def fockMinkowskiPhase (b : Fin 4 → ℝ) (P : Fin 4 → ℝ) : ℂ :=
  Complex.exp (Complex.I * (minkowskiInner P b : ℂ))

lemma continuous_fockMinkowskiPhase (b : Fin 4 → ℝ) :
    Continuous (fockMinkowskiPhase b) := by
  unfold fockMinkowskiPhase
  have h_in : Continuous (fun P : Fin 4 → ℝ => minkowskiInner P b) := by
    simp only [minkowskiInner_explicit]
    exact (((continuous_apply 0).mul continuous_const).sub
      ((continuous_apply 1).mul continuous_const)).sub
      ((continuous_apply 2).mul continuous_const) |>.sub
      ((continuous_apply 3).mul continuous_const)
  exact Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp h_in))

lemma norm_fockMinkowskiPhase (b : Fin 4 → ℝ) (P : Fin 4 → ℝ) :
    ‖fockMinkowskiPhase b P‖ = 1 := by
  unfold fockMinkowskiPhase
  rw [mul_comm, Complex.norm_exp_ofReal_mul_I]

noncomputable def fockMinkowskiTranslate {ν : ℕ} (m : ℝ) (b : Fin 4 → ℝ) :
    FockHilbert ν →L[ℂ] FockHilbert ν :=
  fockMultCLM (fun z => fockMinkowskiPhase b (fockTotalMomentum m z))
    ((continuous_fockMinkowskiPhase b).measurable.comp (measurable_fockTotalMomentum ν m))
    zero_le_one
    (fun z => (norm_fockMinkowskiPhase b (fockTotalMomentum m z)).le)

theorem fockWightmanMap_wightmanConfigTranslate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (b : Fin 4 → ℝ) (A : WightmanConfig ι) :
    fockWightmanMap M_mode hC (wightmanConfigTranslate b A) =
      fockMinkowskiTranslate m b (fockWightmanMap M_mode hC A) := by
  rcases A with ⟨j, α, f⟩
  unfold fockWightmanMap fockSchwartzVec wightmanConfigTranslate fockMinkowskiTranslate
  dsimp only [compactSchwartzTranslate_val]
  have h_eq : ∀ (r : ℕ) (L : PartialPairing j r)
      (p_int : L.InternalChord → Fin 3 → ℝ) (k_ext : Fin r → Fin 3 → ℝ),
      minkowskiFourier (schwartzDiagTranslateN j b f.val) (L.partialMomentum m p_int k_ext) =
        fockMinkowskiPhase b (∑ a : Fin r, massShellVec m (k_ext a)) *
          minkowskiFourier f.val (L.partialMomentum m p_int k_ext) := by
    intro r L p_int k_ext
    rw [minkowskiFourier_schwartzDiagTranslateN, partialMomentum_sum_eq m L p_int k_ext]
    unfold fockMinkowskiPhase
    congr 1
    have h_neg : minkowskiInner (-∑ a : Fin r, massShellVec m (k_ext a)) b =
        -minkowskiInner (∑ a : Fin r, massShellVec m (k_ext a)) b := by
      simp only [minkowskiInner_explicit, Pi.neg_apply]
      ring
    rw [h_neg, Complex.ofReal_neg, mul_neg, neg_neg]
  exact fockMomentumVec_mul_totalMomentum M_mode hC j α
    (partialMomentumBound_minkowskiFourier m j f.val)
    (partialMomentumBound_minkowskiFourier m j (schwartzDiagTranslateN j b f.val))
    (continuous_fockMinkowskiPhase b).measurable zero_le_one
    (fun z => (norm_fockMinkowskiPhase b (fockTotalMomentum m z)).le) h_eq

theorem tendsto_inner_fockMinkowskiTranslate_atTop {ν : ℕ} {m : ℝ} (hm : 0 < m)
    {a : Fin 4 → ℝ} (ha : a ≠ 0) (x y : FockHilbert ν) :
    Tendsto (fun t : ℝ => ⟪x, fockMinkowskiTranslate m (t • a) y⟫_ℂ)
      atTop (𝓝 (⟪x, fockVacuum ν⟫_ℂ * ⟪fockVacuum ν, y⟫_ℂ)) := by
  rw [tendsto_sub_nhds_zero_iff.symm]
  let h : FockOmega ν → ℂ :=
    fun z => star ((x : FockOmega ν → ℂ) z) * (y : FockOmega ν → ℂ) z
  have hh_int : Integrable h (fockMeasure ν) := by
    refine (L2.integrable_inner (𝕜 := ℂ) x y).congr (Filter.Eventually.of_forall (fun z => ?_))
    simp [h, RCLike.inner_apply, mul_comm]
  let F_t : ℝ → FockOmega ν → ℂ := fun t z =>
    (fockMinkowskiPhase (t • a) (fockTotalMomentum m z) -
      (if z.1 = 0 then (1 : ℂ) else 0)) * h z
  have hF_meas : ∀ t : ℝ, AEStronglyMeasurable (F_t t) (fockMeasure ν) := by
    intro t
    have h_ind_eq : (fun z : FockOmega ν => if z.1 = 0 then (1 : ℂ) else 0) =
        sectorToOmega ν 0 (fun _ => (1 : ℂ)) := by
      ext z
      by_cases h0 : z.1 = 0 <;> simp [sectorToOmega, h0]
    have h_ind : Measurable (fun z : FockOmega ν => if z.1 = 0 then (1 : ℂ) else 0) := by
      rw [h_ind_eq]
      exact measurable_sectorToOmega measurable_const
    have h_ph : Measurable (fun z : FockOmega ν =>
        fockMinkowskiPhase (t • a) (fockTotalMomentum m z)) :=
      (continuous_fockMinkowskiPhase (t • a)).measurable.comp (measurable_fockTotalMomentum ν m)
    exact (h_ph.sub h_ind).aestronglyMeasurable.mul hh_int.1
  have hF_le : ∀ (t : ℝ) (z : FockOmega ν), ‖F_t t z‖ ≤ 2 * ‖h z‖ := by
    intro t z
    dsimp [F_t]
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine (norm_sub_le _ _).trans ?_
    rw [norm_fockMinkowskiPhase]
    by_cases h0 : z.1 = 0
    · simp [h0]
      norm_num
    · simp [h0]
  have hF_int : ∀ t : ℝ, Integrable (F_t t) (fockMeasure ν) :=
    fun t => (hh_int.norm.const_mul 2).mono' (hF_meas t)
      (Filter.Eventually.of_forall (hF_le t))
  have h_diff_eq : ∀ t : ℝ,
      ⟪x, fockMinkowskiTranslate m (t • a) y⟫_ℂ -
        ⟪x, fockVacuum ν⟫_ℂ * ⟪fockVacuum ν, y⟫_ℂ =
      ∑' r : ℕ, ∫ w : FockSectorDom ν r, F_t t ⟨r, w⟩ ∂(fockSectorMeasure ν r) := by
    intro t
    unfold fockMinkowskiTranslate
    rw [inner_fockMultCLM_right, inner_fockVacuum_mul_eq_integral,
        ← integral_sub (by
          refine hh_int.norm.mono'
            (((continuous_fockMinkowskiPhase (t • a)).measurable.comp
              (measurable_fockTotalMomentum ν m)).aestronglyMeasurable.mul hh_int.1)
            (Filter.Eventually.of_forall (fun z => ?_))
          rw [norm_mul, norm_fockMinkowskiPhase, one_mul])
          (integrable_sectorZero_mul_of_integrable hh_int)]
    have h_sub : (fun z : FockOmega ν =>
        fockMinkowskiPhase (t • a) (fockTotalMomentum m z) * h z -
          (if z.1 = 0 then (1 : ℂ) else 0) * h z) = F_t t := by
      ext z
      dsimp [F_t]
      ring
    rw [h_sub]
    have h_int_sum := hF_int t
    unfold fockMeasure at h_int_sum ⊢
    rw [integral_sum_measure h_int_sum]
    refine tsum_congr (fun r => ?_)
    have hr_int : Integrable (F_t t) ((fockSectorMeasure ν r).map (Sigma.mk r)) :=
      h_int_sum.mono_measure (Measure.le_sum _ r)
    exact integral_map (measurable_fockSigmaMk ν r).aemeasurable hr_int.1
  rw [funext h_diff_eq]
  let B_sec : ℕ → ℝ := fun r =>
    ∫ z : FockOmega ν, 2 * ‖h z‖ ∂((fockSectorMeasure ν r).map (Sigma.mk r))
  have hB_summable : Summable B_sec := by
    have hh2 : Integrable (fun z : FockOmega ν => 2 * ‖h z‖) (fockMeasure ν) :=
      hh_int.norm.const_mul 2
    unfold fockMeasure at hh2
    exact (hasSum_integral_measure hh2).summable
  have hB_eq : ∀ r : ℕ, B_sec r =
      ∫ w : FockSectorDom ν r, 2 * ‖h ⟨r, w⟩‖ ∂(fockSectorMeasure ν r) := by
    intro r
    have hr_int : Integrable (fun z : FockOmega ν => 2 * ‖h z‖)
        ((fockSectorMeasure ν r).map (Sigma.mk r)) :=
      (hh_int.norm.const_mul 2).mono_measure (Measure.le_sum _ r)
    exact integral_map (measurable_fockSigmaMk ν r).aemeasurable hr_int.1
  have h0_tsum : (0 : ℂ) = ∑' _ : ℕ, (0 : ℂ) := tsum_zero.symm
  rw [h0_tsum]
  refine tendsto_tsum_of_dominated_convergence hB_summable (fun r => ?_)
    (Filter.Eventually.of_forall (fun t r => ?_))
  · cases r with
    | zero =>
      have h0 : (fun t : ℝ =>
          ∫ w : FockSectorDom ν 0, F_t t ⟨0, w⟩ ∂(fockSectorMeasure ν 0)) = fun _ => 0 := by
        ext t
        have hw0 : (fun w : FockSectorDom ν 0 => F_t t ⟨0, w⟩) = fun _ => 0 := by
          ext w
          simp [F_t, fockMinkowskiPhase, minkowskiInner_explicit]
        rw [hw0, integral_zero]
      rw [h0]
      exact tendsto_const_nhds
    | succ r' =>
      have hh_sec : Integrable (fun w : FockSectorDom ν (r' + 1) => h ⟨r' + 1, w⟩)
          (fockSectorMeasure ν (r' + 1)) := by
        have hm_map : Integrable h ((fockSectorMeasure ν (r' + 1)).map (Sigma.mk (r' + 1))) :=
          hh_int.mono_measure (Measure.le_sum _ (r' + 1))
        exact (integrable_map_measure hm_map.1
          (measurable_fockSigmaMk ν (r' + 1)).aemeasurable).mp hm_map
      have hF_sec : ∀ t : ℝ, Integrable (fun w : FockSectorDom ν (r' + 1) => F_t t ⟨r' + 1, w⟩)
          (fockSectorMeasure ν (r' + 1)) := by
        intro t
        have hm_map : Integrable (F_t t)
            ((fockSectorMeasure ν (r' + 1)).map (Sigma.mk (r' + 1))) :=
          (hF_int t).mono_measure (Measure.le_sum _ (r' + 1))
        exact (integrable_map_measure hm_map.1
          (measurable_fockSigmaMk ν (r' + 1)).aemeasurable).mp hm_map
      have h_fub_s : ∀ t : ℝ,
          (∫ w : FockSectorDom ν (r' + 1), F_t t ⟨r' + 1, w⟩
            ∂(fockSectorMeasure ν (r' + 1))) =
          ∑ s : Fin (r' + 1) → Fin ν,
            ∫ k : Fin (r' + 1) → Fin 3 → ℝ, F_t t ⟨r' + 1, (k, s)⟩ := by
        intro t
        have hf := hF_sec t
        unfold fockSectorMeasure at hf ⊢
        rw [integral_prod_symm _ hf, integral_fintype_count]
      rw [funext h_fub_s]
      have hh_s_ae : ∀ᵐ s : Fin (r' + 1) → Fin ν ∂Measure.count,
          Integrable (fun k : Fin (r' + 1) → Fin 3 → ℝ => h ⟨r' + 1, (k, s)⟩) volume := by
        unfold fockSectorMeasure at hh_sec
        exact ((integrable_prod_iff' hh_sec.1).mp hh_sec).1
      have hh_s : ∀ s : Fin (r' + 1) → Fin ν,
          Integrable (fun k : Fin (r' + 1) → Fin 3 → ℝ => h ⟨r' + 1, (k, s)⟩) volume := by
        rwa [Measure.ae_count_iff] at hh_s_ae
      have h0_sum : (0 : ℂ) = ∑ _ : Fin (r' + 1) → Fin ν, (0 : ℂ) :=
        Finset.sum_const_zero.symm
      rw [h0_sum]
      refine tendsto_finsetSum (Finset.univ : Finset (Fin (r' + 1) → Fin ν)) (fun s _ => ?_)
      let mp := (volume_preserving_piFinSuccAbove
        (fun _ : Fin (r' + 1) => Fin 3 → ℝ) 0).symm
      let e := (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (r' + 1) => Fin 3 → ℝ) 0).symm
      have h_hs_prod : Integrable
          (fun qk : (Fin 3 → ℝ) × (Fin r' → Fin 3 → ℝ) => h ⟨r' + 1, (e qk, s)⟩)
          (volume.prod volume) :=
        (mp.integrable_comp_emb e.measurableEmbedding).mpr (hh_s s)
      have h_Fs_prod : ∀ t : ℝ, Integrable
          (fun qk : (Fin 3 → ℝ) × (Fin r' → Fin 3 → ℝ) => F_t t ⟨r' + 1, (e qk, s)⟩)
          (volume.prod volume) := by
        intro t
        have hFs_ae : ∀ᵐ s' : Fin (r' + 1) → Fin ν ∂Measure.count,
            Integrable (fun k : Fin (r' + 1) → Fin 3 → ℝ =>
              F_t t ⟨r' + 1, (k, s')⟩) volume := by
          have hf := hF_sec t
          unfold fockSectorMeasure at hf
          exact ((integrable_prod_iff' hf.1).mp hf).1
        rw [Measure.ae_count_iff] at hFs_ae
        exact (mp.integrable_comp_emb e.measurableEmbedding).mpr (hFs_ae s)
      have h_split_k : ∀ t : ℝ,
          (∫ k : Fin (r' + 1) → Fin 3 → ℝ, F_t t ⟨r' + 1, (k, s)⟩) =
          ∫ k' : Fin r' → Fin 3 → ℝ,
            (∫ q : Fin 3 → ℝ, F_t t ⟨r' + 1, (e (q, k'), s)⟩) := by
        intro t
        rw [← mp.integral_comp']
        exact integral_prod_symm _ (h_Fs_prod t)
      rw [funext h_split_k]
      have h_dom_k' : Integrable
          (fun k' : Fin r' → Fin 3 → ℝ => ∫ q : Fin 3 → ℝ, ‖h ⟨r' + 1, (e (q, k'), s)⟩‖)
          volume :=
        h_hs_prod.norm.integral_prod_right
      have h_ae_k' : ∀ᵐ k' : Fin r' → Fin 3 → ℝ ∂volume,
          Integrable (fun q : Fin 3 → ℝ => h ⟨r' + 1, (e (q, k'), s)⟩) volume :=
        ((integrable_prod_iff' h_hs_prod.1).mp h_hs_prod).1
      have h0_k' : (0 : ℂ) = ∫ _ : Fin r' → Fin 3 → ℝ, (0 : ℂ) := by simp
      rw [h0_k']
      refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (fun k' => ∫ q : Fin 3 → ℝ, ‖h ⟨r' + 1, (e (q, k'), s)⟩‖) ?_ ?_ h_dom_k' ?_
      · exact Filter.Eventually.of_forall (fun t => (h_Fs_prod t).integral_prod_right.1)
      · refine Filter.Eventually.of_forall (fun t => Filter.Eventually.of_forall (fun k' => ?_))
        refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
          (Filter.Eventually.of_forall (fun q => ?_))))
        dsimp [F_t]
        simp only [sub_zero, norm_mul, norm_fockMinkowskiPhase, one_mul]
      · filter_upwards [h_ae_k'] with k' hk'
        let P_rest : Fin 4 → ℝ := ∑ i : Fin r', massShellVec m (k' i)
        have h_fac : ∀ t : ℝ,
            (∫ q : Fin 3 → ℝ, F_t t ⟨r' + 1, (e (q, k'), s)⟩) =
            fockMinkowskiPhase (t • a) P_rest *
              ∫ q : Fin 3 → ℝ, h ⟨r' + 1, (e (q, k'), s)⟩ *
                Complex.exp (Complex.I * (t : ℂ) *
                  (minkowskiInner (massShellVec m q) a : ℂ)) := by
          intro t
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall (fun q => ?_))
          dsimp only [F_t]
          simp only [Nat.succ_ne_zero, ↓reduceIte, sub_zero]
          have he_cons : e (q, k') = Fin.cons q k' := by
            ext i
            refine Fin.cases ?_ ?_ i <;> simp [e]
          have h_tot : fockTotalMomentum m ⟨r' + 1, (e (q, k'), s)⟩ =
              massShellVec m q + P_rest := by
            unfold fockTotalMomentum
            dsimp only
            rw [he_cons, Fin.sum_univ_succ]
            simp [P_rest]
          have h_ph_mul : fockMinkowskiPhase (t • a) (massShellVec m q + P_rest) =
              fockMinkowskiPhase (t • a) P_rest *
                Complex.exp (Complex.I * (t : ℂ) *
                  (minkowskiInner (massShellVec m q) a : ℂ)) := by
            unfold fockMinkowskiPhase
            rw [← Complex.exp_add]
            congr 1
            have h_lin : minkowskiInner (massShellVec m q + P_rest) (t • a) =
                minkowskiInner P_rest (t • a) +
                  t * minkowskiInner (massShellVec m q) a := by
              simp only [minkowskiInner_explicit, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              ring
            rw [h_lin]
            push_cast
            ring
          rw [h_tot, h_ph_mul]
          ring
        rw [funext h_fac]
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have h_osc := (tendsto_zero_iff_norm_tendsto_zero.mp
          (tendsto_massShell_oscillatory hm ha hk'))
        refine h_osc.congr (fun t => ?_)
        rw [norm_mul, norm_fockMinkowskiPhase, one_mul]
  · rw [hB_eq r]
    have h_dom_sec : Integrable (fun w : FockSectorDom ν r => 2 * ‖h ⟨r, w⟩‖)
        (fockSectorMeasure ν r) := by
      have hm_map : Integrable (fun z : FockOmega ν => 2 * ‖h z‖)
          ((fockSectorMeasure ν r).map (Sigma.mk r)) :=
        (hh_int.norm.const_mul 2).mono_measure (Measure.le_sum _ r)
      exact (integrable_map_measure hm_map.1
        (measurable_fockSigmaMk ν r).aemeasurable).mp hm_map
    exact (norm_integral_le_integral_norm _).trans
      (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
        h_dom_sec (Filter.Eventually.of_forall (fun w => hF_le t ⟨r, w⟩)))

theorem wickMassShellWightmanClusterAlong {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (WData : WightmanPositiveData R_rep S)
    (hW : WData.W = wickMassShellW m η C hC)
    {a : Fin 4 → ℝ} (ha : a ≠ 0) :
    WightmanClusterAlong WData a := by
  have htr : WightmanTranslationInvariant WData.W := by
    rw [hW]
    exact wightmanTranslationInvariant_of_tubeTranslationInvariant
      (wickMassShellTubeExtension m hm η C hC)
      (wickMassShellTubeTranslationInvariant hm η hC)
  have h_ker : ∀ A B : WightmanConfig ι,
      ⟪fockWightmanMap M_mode hC A, fockWightmanMap M_mode hC B⟫_ℂ =
        wightmanKernel S WData.W A B := by
    intro A B
    rw [hW]
    exact inner_fockWightmanMap_eq_wightmanKernel M_mode hC hC_herm A B
  let ι_W := wavepacketWightmanLinearIsometry WData (fockWightmanMap M_mode hC) h_ker
  have hvac : ι_W (wightmanVacuum WData) = fockVacuum M_mode.ν :=
    (wavepacketWightmanLinearIsometry_wightmanVacuum WData
      (fockWightmanMap M_mode hC) h_ker).trans
      (fockWightmanMap_wightmanVacuumConfig M_mode hC)
  exact wightmanClusterAlong_of_linearIsometry WData htr ι_W hvac
    (fockMinkowskiTranslate m)
    (wavepacketWightmanLinearIsometry_intertwines_translate WData htr
      (fockWightmanMap M_mode hC) h_ker (fockMinkowskiTranslate m)
      (fockWightmanMap_wightmanConfigTranslate M_mode hC))
    (tendsto_inner_fockMinkowskiTranslate_atTop hm ha)

theorem wickMassShellWightmanVacuumUnique {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (WData : WightmanPositiveData R_rep S)
    (hW : WData.W = wickMassShellW m η C hC)
    (htrans : WightmanTranslationInvariant WData.W) :
    WightmanVacuumUnique WData htrans := by
  have ha : euclidTimeVec 1 ≠ 0 := by
    intro h0
    have h1 : euclidTimeVec 1 0 = (0 : Fin 4 → ℝ) 0 := congrArg (fun v => v 0) h0
    norm_num [euclidTimeVec] at h1
  exact wightmanVacuumUnique_of_clusterAlong WData htrans
    (wickMassShellWightmanClusterAlong hm M_mode hC hC_herm WData hW ha)

theorem wickMassShellWightmanVacuumNormalized {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q) :
    WightmanVacuumNormalized S (wickMassShellW m η C hC) := by
  let WData := wightmanPositiveDataOfPositivity S (wickMassShellW m η C hC)
    (wickMassShellPositivity M_mode hC hC_herm)
  have h_ker : ∀ A B : WightmanConfig ι,
      ⟪fockWightmanMap M_mode hC A, fockWightmanMap M_mode hC B⟫_ℂ =
        wightmanKernel S WData.W A B :=
    inner_fockWightmanMap_eq_wightmanKernel M_mode hC hC_herm
  let ι_W := wavepacketWightmanLinearIsometry WData (fockWightmanMap M_mode hC) h_ker
  have hvac : ι_W (wightmanVacuum WData) = fockVacuum M_mode.ν :=
    (wavepacketWightmanLinearIsometry_wightmanVacuum WData
      (fockWightmanMap M_mode hC) h_ker).trans
      (fockWightmanMap_wightmanVacuumConfig M_mode hC)
  exact wightmanVacuumNormalized_of_linearIsometry WData ι_W hvac (inner_fockVacuum_self M_mode.ν)

lemma ChordPairing.card_chord_eq {n : ℕ} (P : ChordPairing n) :
    Fintype.card P.Chord = n / 2 := by
  have h := P.two_mul_card_chord
  omega

noncomputable def toChordMom {n : ℕ} (P : ChordPairing n) :
    (Fin (n / 2) → Fin 3 → ℝ) ≃ᵐ (P.Chord → Fin 3 → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : P.Chord => Fin 3 → ℝ)
    (Fintype.equivFinOfCardEq P.card_chord_eq).symm

lemma measurePreserving_toChordMom {n : ℕ} (P : ChordPairing n) :
    MeasurePreserving (toChordMom P) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ : P.Chord => Fin 3 → ℝ)
    (Fintype.equivFinOfCardEq P.card_chord_eq).symm

instance instMeasChordPairing (n : ℕ) : MeasurableSpace (ChordPairing n) := ⊤

instance instMeasurableSingletonChordPairing (n : ℕ) :
    MeasurableSingletonClass (ChordPairing n) :=
  ⟨fun _ => trivial⟩

abbrev WickSpectralIndex (n : ℕ) : Type :=
  ChordPairing n × (Fin (n / 2) → Fin 3 → ℝ)

noncomputable def wickSpectralMeasure (n : ℕ) : Measure (WickSpectralIndex n) :=
  Measure.count.prod volume

lemma measurable_wickSpectralIndex {n : ℕ} {β : Type*} [MeasurableSpace β]
    {Φ : ChordPairing n → (Fin (n / 2) → Fin 3 → ℝ) → β}
    (hΦ : ∀ P : ChordPairing n, Measurable (Φ P)) :
    Measurable (fun a : WickSpectralIndex n => Φ a.1 a.2) := by
  intro U hU
  have h_pre :
      (fun a : WickSpectralIndex n => Φ a.1 a.2) ⁻¹' U =
        ⋃ P : ChordPairing n, ({P} : Set (ChordPairing n)) ×ˢ (Φ P ⁻¹' U) := by
    ext ⟨P, q⟩
    simp
  rw [h_pre]
  exact MeasurableSet.iUnion (fun P => MeasurableSet.prod trivial (hΦ P hU))

lemma integrable_wickSpectralMeasure {n : ℕ}
    {Φ : ∀ P : ChordPairing n, (P.Chord → Fin 3 → ℝ) → ℂ}
    (hΦ_meas : ∀ P : ChordPairing n, Measurable (Φ P))
    (hΦ_int : ∀ P : ChordPairing n, Integrable (Φ P) volume) :
    Integrable (fun a : WickSpectralIndex n => Φ a.1 (toChordMom a.1 a.2))
      (wickSpectralMeasure n) := by
  have h_meas := measurable_wickSpectralIndex
    (fun P => (hΦ_meas P).comp (toChordMom P).measurable)
  unfold wickSpectralMeasure
  refine (integrable_prod_iff h_meas.aestronglyMeasurable).mpr
    ⟨Filter.Eventually.of_forall (fun P => ?_), Integrable.of_finite⟩
  exact ((measurePreserving_toChordMom P).integrable_comp_emb
    (toChordMom P).measurableEmbedding).mpr (hΦ_int P)

lemma integral_wickSpectralMeasure {n : ℕ}
    {Φ : ∀ P : ChordPairing n, (P.Chord → Fin 3 → ℝ) → ℂ}
    (hΦ_meas : ∀ P : ChordPairing n, Measurable (Φ P))
    (hΦ_int : ∀ P : ChordPairing n, Integrable (Φ P) volume) :
    (∫ a : WickSpectralIndex n, Φ a.1 (toChordMom a.1 a.2) ∂(wickSpectralMeasure n)) =
      ∑ P : ChordPairing n, ∫ q : P.Chord → Fin 3 → ℝ, Φ P q := by
  have h_int := integrable_wickSpectralMeasure hΦ_meas hΦ_int
  unfold wickSpectralMeasure at h_int ⊢
  rw [integral_prod _ h_int, integral_fintype_count]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  exact (measurePreserving_toChordMom P).integral_comp' (Φ P)

theorem integrable_wickChordWeight_mul_vladimirov_kernel {κ : Type*} {n : ℕ} {m : ℝ}
    (hm : 0 < m) {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (P : ChordPairing n) (α : Fin n → κ)
    {z : Fin n → Fin 4 → ℂ} (hz : z ∈ forward_tube_n n) :
    Integrable (fun q : P.Chord → Fin 3 → ℝ =>
      wickChordWeight m C P α q * vladimirov_kernel n z (P.momentum m q)) volume := by
  have h_prod : Integrable
      (fun q : P.Chord → Fin 3 → ℝ =>
        ∏ c : P.Chord,
          (massShellWeight m C ![α c.1, α (P.mate c.1)] (q c) *
            vladimirov_kernel 2 ![z c.1, z (P.mate c.1)]
              (twoPointMomentum (massShellVec m (q c)))))
      volume :=
    Integrable.fintype_prod
      (f := fun c : P.Chord => fun p : Fin 3 → ℝ =>
        massShellWeight m C ![α c.1, α (P.mate c.1)] p *
          vladimirov_kernel 2 ![z c.1, z (P.mate c.1)]
            (twoPointMomentum (massShellVec m p)))
      (fun c => integrable_massShellWeight_mul_kernel hm hC
        ![α c.1, α (P.mate c.1)] (pair_mem_forward_tube_two hz c.2))
  refine h_prod.congr (Filter.Eventually.of_forall (fun q => ?_))
  dsimp only [wickChordWeight]
  rw [Finset.prod_mul_distrib, ← P.vladimirov_kernel_momentum m z q]

noncomputable def wickTemperedSpectralMeasureFamily {ι : Type*} (m : ℝ) (hm : 0 < m)
    (η : ℂ) (C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C) :
    TemperedForwardConeSpectralMeasureFamily ι where
  A n := WickSpectralIndex n
  instMeas _ := inferInstance
  μ n := wickSpectralMeasure n
  instSFinite n := by
    unfold wickSpectralMeasure
    infer_instance
  ρ n α a := η ^ a.1.cross * wickChordWeight m C a.1 α (toChordMom a.1 a.2)
  p _ _ a := a.1.momentum m (toChordMom a.1 a.2)
  measurable_p n _ :=
    measurable_wickSpectralIndex (fun P => (P.measurable_momentum m).comp (toChordMom P).measurable)
  mem_forwardCone _ _ a :=
    a.1.momentum_mem_forwardConeSpectralRegion hm (toChordMom a.1 a.2)
  integrable_ρ_mul_schwartz n α g := by
    let Φ : ∀ P : ChordPairing n, (P.Chord → Fin 3 → ℝ) → ℂ :=
      fun P q => η ^ P.cross * (wickChordWeight m C P α q *
        g (momentumToEuclidCLMN n (P.momentum m q)))
    have hΦ_meas : ∀ P : ChordPairing n, Measurable (Φ P) :=
      fun P => measurable_const.mul ((measurable_wickChordWeight hC P α).mul
        ((g.continuous.comp (momentumToEuclidCLMN n).continuous).measurable.comp
          (P.measurable_momentum m)))
    have hΦ_int : ∀ P : ChordPairing n, Integrable (Φ P) volume :=
      fun P => (integrable_wickChordWeight_mul_schwartz hC P α g).const_mul (η ^ P.cross)
    refine (integrable_wickSpectralMeasure hΦ_meas hΦ_int).congr
      (Filter.Eventually.of_forall (fun a => ?_))
    dsimp [Φ]
    ring
  schwartz_seminorm_bound n α := by
    let s : Finset (ℕ × ℕ) := Finset.Iic (4 * (n / 2), 0)
    let B_fn : ChordPairing n → ℝ :=
      fun P => Classical.choose (exists_norm_wickChordWeight_le hC P α)
    have hB_fn : ∀ P : ChordPairing n,
        0 ≤ B_fn P ∧ ∀ q : P.Chord → Fin 3 → ℝ, ‖wickChordWeight m C P α q‖ ≤ B_fn P :=
      fun P => Classical.choose_spec (exists_norm_wickChordWeight_le hC P α)
    let I_fn : ChordPairing n → ℝ :=
      fun P => ∫ q : P.Chord → Fin 3 → ℝ, ∏ c : P.Chord, ((1 + ‖q c‖) ^ 4)⁻¹
    have hI_nn : ∀ P : ChordPairing n, 0 ≤ I_fn P :=
      fun P => integral_nonneg (fun _ => Finset.prod_nonneg (fun _ _ => by positivity))
    let C_fn : ChordPairing n → ℝ :=
      fun P => ‖η ^ P.cross‖ * (B_fn P * (4 * Real.pi) ^ (4 * (n / 2)) * I_fn P)
    have hC_nn : ∀ P : ChordPairing n, 0 ≤ C_fn P := fun P => by
      have hB := (hB_fn P).1
      have hI := hI_nn P
      positivity
    refine ⟨s, ∑ P : ChordPairing n, C_fn P, Finset.sum_nonneg (fun P _ => hC_nn P), fun g => ?_⟩
    let Φ : ∀ P : ChordPairing n, (P.Chord → Fin 3 → ℝ) → ℂ :=
      fun P q => η ^ P.cross * (wickChordWeight m C P α q *
        g (momentumToEuclidCLMN n (P.momentum m q)))
    have hΦ_meas : ∀ P : ChordPairing n, Measurable (Φ P) :=
      fun P => measurable_const.mul ((measurable_wickChordWeight hC P α).mul
        ((g.continuous.comp (momentumToEuclidCLMN n).continuous).measurable.comp
          (P.measurable_momentum m)))
    have hΦ_int : ∀ P : ChordPairing n, Integrable (Φ P) volume :=
      fun P => (integrable_wickChordWeight_mul_schwartz hC P α g).const_mul (η ^ P.cross)
    have h_eq :
        (∫ a : WickSpectralIndex n,
          (η ^ a.1.cross * wickChordWeight m C a.1 α (toChordMom a.1 a.2)) *
            g (momentumToEuclidCLMN n (a.1.momentum m (toChordMom a.1 a.2)))
          ∂(wickSpectralMeasure n)) =
        ∑ P : ChordPairing n, η ^ P.cross *
          ∫ q : P.Chord → Fin 3 → ℝ,
            wickChordWeight m C P α q * g (momentumToEuclidCLMN n (P.momentum m q)) := by
      have h_congr :
          (fun a : WickSpectralIndex n =>
            (η ^ a.1.cross * wickChordWeight m C a.1 α (toChordMom a.1 a.2)) *
              g (momentumToEuclidCLMN n (a.1.momentum m (toChordMom a.1 a.2)))) =
          fun a => Φ a.1 (toChordMom a.1 a.2) := by
        ext a
        dsimp [Φ]
        ring
      rw [h_congr, integral_wickSpectralMeasure hΦ_meas hΦ_int]
      refine Finset.sum_congr rfl (fun P _ => ?_)
      exact integral_const_mul (η ^ P.cross) _
    rw [h_eq]
    let S_val : ℝ := s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ) g
    calc ‖∑ P : ChordPairing n, η ^ P.cross *
            ∫ q : P.Chord → Fin 3 → ℝ,
              wickChordWeight m C P α q * g (momentumToEuclidCLMN n (P.momentum m q))‖
        ≤ ∑ P : ChordPairing n, ‖η ^ P.cross *
            ∫ q : P.Chord → Fin 3 → ℝ,
              wickChordWeight m C P α q * g (momentumToEuclidCLMN n (P.momentum m q))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ P : ChordPairing n, C_fn P * S_val := by
          refine Finset.sum_le_sum (fun P _ => ?_)
          rw [norm_mul]
          dsimp [C_fn]
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have h_each :
              ‖∫ q : P.Chord → Fin 3 → ℝ,
                  wickChordWeight m C P α q * g (momentumToEuclidCLMN n (P.momentum m q))‖ ≤
                (B_fn P * ((4 * Real.pi) ^ (4 * (n / 2)) * S_val)) * I_fn P := by
            calc ‖∫ q : P.Chord → Fin 3 → ℝ,
                    wickChordWeight m C P α q * g (momentumToEuclidCLMN n (P.momentum m q))‖
                ≤ ∫ q : P.Chord → Fin 3 → ℝ,
                    ‖wickChordWeight m C P α q * g (momentumToEuclidCLMN n (P.momentum m q))‖ :=
                  norm_integral_le_integral_norm _
              _ ≤ ∫ q : P.Chord → Fin 3 → ℝ,
                    (B_fn P * ((4 * Real.pi) ^ (4 * (n / 2)) * S_val)) *
                      ∏ c : P.Chord, ((1 + ‖q c‖) ^ 4)⁻¹ := by
                  refine integral_mono_of_nonneg
                    (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
                    ((integrable_chordDecay P).const_mul _)
                    (Filter.Eventually.of_forall (fun q => ?_))
                  dsimp only
                  rw [norm_mul]
                  have h_sch := P.norm_schwartz_momentumToEuclid_chord_le m g q
                  rw [P.card_chord_eq] at h_sch
                  calc ‖wickChordWeight m C P α q‖ *
                        ‖g (momentumToEuclidCLMN n (P.momentum m q))‖
                      ≤ B_fn P * (((4 * Real.pi) ^ (4 * (n / 2)) * S_val) *
                          ∏ c : P.Chord, ((1 + ‖q c‖) ^ 4)⁻¹) :=
                        mul_le_mul ((hB_fn P).2 q) h_sch (norm_nonneg _) (hB_fn P).1
                    _ = (B_fn P * ((4 * Real.pi) ^ (4 * (n / 2)) * S_val)) *
                          ∏ c : P.Chord, ((1 + ‖q c‖) ^ 4)⁻¹ := by ring
              _ = (B_fn P * ((4 * Real.pi) ^ (4 * (n / 2)) * S_val)) * I_fn P :=
                  integral_const_mul _ _
          exact h_each.trans_eq (by ring)
      _ = (∑ P : ChordPairing n, C_fn P) * S_val := (Finset.sum_mul _ _ _).symm
  analyticOn_H_raw n α := by
    refine (analyticOn_wickMassShellH hm η hC n α).congr (fun z hz => ?_)
    let Φ : ∀ P : ChordPairing n, (P.Chord → Fin 3 → ℝ) → ℂ :=
      fun P q => η ^ P.cross * (wickChordWeight m C P α q *
        vladimirov_kernel n z (P.momentum m q))
    have hΦ_meas : ∀ P : ChordPairing n, Measurable (Φ P) :=
      fun P => measurable_const.mul ((measurable_wickChordWeight hC P α).mul
        ((vladimirov_kernel_contDiff n z).continuous.measurable.comp
          (P.measurable_momentum m)))
    have hΦ_int : ∀ P : ChordPairing n, Integrable (Φ P) volume :=
      fun P => (integrable_wickChordWeight_mul_vladimirov_kernel hm hC P α hz).const_mul
        (η ^ P.cross)
    have h_congr :
        (fun a : WickSpectralIndex n =>
          (η ^ a.1.cross * wickChordWeight m C a.1 α (toChordMom a.1 a.2)) *
            vladimirov_kernel n z (a.1.momentum m (toChordMom a.1 a.2))) =
        fun a => Φ a.1 (toChordMom a.1 a.2) := by
      ext a
      dsimp [Φ]
      ring
    rw [h_congr, integral_wickSpectralMeasure hΦ_meas hΦ_int, wickMassShellH_eq_sum_integral]
    exact Finset.sum_congr rfl (fun P _ => integral_const_mul (η ^ P.cross) _)
  tendsto_boundary n α f _v hv := by
    have h_rhs :
        (∫ a : WickSpectralIndex n,
          (η ^ a.1.cross * wickChordWeight m C a.1 α (toChordMom a.1 a.2)) *
            minkowskiFourier f (a.1.momentum m (toChordMom a.1 a.2))
          ∂(wickSpectralMeasure n)) =
        wickMassShellW m η C hC n α f := by
      let Φ : ∀ P : ChordPairing n, (P.Chord → Fin 3 → ℝ) → ℂ :=
        fun P q => η ^ P.cross * (wickChordWeight m C P α q *
          minkowskiFourier f (P.momentum m q))
      have hΦ_meas : ∀ P : ChordPairing n, Measurable (Φ P) :=
        fun P => measurable_const.mul ((measurable_wickChordWeight hC P α).mul
          ((continuous_minkowskiFourier n f).measurable.comp (P.measurable_momentum m)))
      have hΦ_int : ∀ P : ChordPairing n, Integrable (Φ P) volume :=
        fun P => (integrable_wickChordWeight_mul_minkowskiFourier hC P α f).const_mul
          (η ^ P.cross)
      have h_congr :
          (fun a : WickSpectralIndex n =>
            (η ^ a.1.cross * wickChordWeight m C a.1 α (toChordMom a.1 a.2)) *
              minkowskiFourier f (a.1.momentum m (toChordMom a.1 a.2))) =
          fun a => Φ a.1 (toChordMom a.1 a.2) := by
        ext a
        dsimp [Φ]
        ring
      rw [h_congr, integral_wickSpectralMeasure hΦ_meas hΦ_int, wickMassShellW_apply]
      exact Finset.sum_congr rfl (fun P _ => integral_const_mul (η ^ P.cross) _)
    rw [h_rhs]
    refine (tendsto_wickMassShellH_boundary hm η hC n α f hv).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => congrArg (· * f x) ?_))
    have hz : tubeBoundaryLine n x _v t ∈ forward_tube_n n :=
      line_mem_forward_tube n x _v hv t ht
    let Φ : ∀ P : ChordPairing n, (P.Chord → Fin 3 → ℝ) → ℂ :=
      fun P q => η ^ P.cross * (wickChordWeight m C P α q *
        vladimirov_kernel n (tubeBoundaryLine n x _v t) (P.momentum m q))
    have hΦ_meas : ∀ P : ChordPairing n, Measurable (Φ P) :=
      fun P => measurable_const.mul ((measurable_wickChordWeight hC P α).mul
        ((vladimirov_kernel_contDiff n (tubeBoundaryLine n x _v t)).continuous.measurable.comp
          (P.measurable_momentum m)))
    have hΦ_int : ∀ P : ChordPairing n, Integrable (Φ P) volume :=
      fun P => (integrable_wickChordWeight_mul_vladimirov_kernel hm hC P α hz).const_mul
        (η ^ P.cross)
    have h_congr :
        (fun a : WickSpectralIndex n =>
          (η ^ a.1.cross * wickChordWeight m C a.1 α (toChordMom a.1 a.2)) *
            vladimirov_kernel n (tubeBoundaryLine n x _v t)
              (a.1.momentum m (toChordMom a.1 a.2))) =
        fun a => Φ a.1 (toChordMom a.1 a.2) := by
      ext a
      dsimp [Φ]
      ring
    rw [h_congr, integral_wickSpectralMeasure hΦ_meas hΦ_int, wickMassShellH_eq_sum_integral]
    exact (Finset.sum_congr rfl (fun P _ => integral_const_mul (η ^ P.cross) _)).symm

@[simp]
theorem wickTemperedSpectralMeasureFamily_toWightmanFamily {ι : Type*}
    (m : ℝ) (hm : 0 < m) (η : ℂ) (C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ)
    (hC : MassShellCoeffData m C) :
    (wickTemperedSpectralMeasureFamily m hm η C hC).toWightmanFamily =
      wickMassShellW m η C hC := by
  ext n α f
  rw [TemperedForwardConeSpectralMeasureFamily.toWightmanFamily_apply, wickMassShellW_apply]
  let Φ : ∀ P : ChordPairing n, (P.Chord → Fin 3 → ℝ) → ℂ :=
    fun P q => η ^ P.cross * (wickChordWeight m C P α q * minkowskiFourier f (P.momentum m q))
  have hΦ_meas : ∀ P : ChordPairing n, Measurable (Φ P) :=
    fun P => measurable_const.mul ((measurable_wickChordWeight hC P α).mul
      ((continuous_minkowskiFourier n f).measurable.comp (P.measurable_momentum m)))
  have hΦ_int : ∀ P : ChordPairing n, Integrable (Φ P) volume :=
    fun P => (integrable_wickChordWeight_mul_minkowskiFourier hC P α f).const_mul (η ^ P.cross)
  have h_congr :
      (fun a : (wickTemperedSpectralMeasureFamily m hm η C hC).A n =>
        (wickTemperedSpectralMeasureFamily m hm η C hC).ρ n α a *
          minkowskiFourier f ((wickTemperedSpectralMeasureFamily m hm η C hC).p n α a)) =
      fun a => Φ a.1 (toChordMom a.1 a.2) := by
    ext a
    dsimp [wickTemperedSpectralMeasureFamily, Φ]
    ring
  rw [h_congr]
  change (∫ a : WickSpectralIndex n, Φ a.1 (toChordMom a.1 a.2) ∂(wickSpectralMeasure n)) = _
  rw [integral_wickSpectralMeasure hΦ_meas hΦ_int]
  exact Finset.sum_congr rfl (fun P _ => integral_const_mul (η ^ P.cross) _)

theorem wickTemperedSpectralMeasureFamily_H {ι : Type*}
    (m : ℝ) (hm : 0 < m) (η : ℂ) (C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ)
    (hC : MassShellCoeffData m C) (n : ℕ) (α : Fin n → ι)
    {z : Fin n → Fin 4 → ℂ} (hz : z ∈ forward_tube_n n) :
    (wickTemperedSpectralMeasureFamily m hm η C hC).H n α z =
      wickMassShellH m η C n α z := by
  unfold TemperedForwardConeSpectralMeasureFamily.H
  let Φ : ∀ P : ChordPairing n, (P.Chord → Fin 3 → ℝ) → ℂ :=
    fun P q => η ^ P.cross * (wickChordWeight m C P α q *
      vladimirov_kernel n z (P.momentum m q))
  have hΦ_meas : ∀ P : ChordPairing n, Measurable (Φ P) :=
    fun P => measurable_const.mul ((measurable_wickChordWeight hC P α).mul
      ((vladimirov_kernel_contDiff n z).continuous.measurable.comp
        (P.measurable_momentum m)))
  have hΦ_int : ∀ P : ChordPairing n, Integrable (Φ P) volume :=
    fun P => (integrable_wickChordWeight_mul_vladimirov_kernel hm hC P α hz).const_mul
      (η ^ P.cross)
  have h_congr :
      (fun a : (wickTemperedSpectralMeasureFamily m hm η C hC).A n =>
        (wickTemperedSpectralMeasureFamily m hm η C hC).ρ n α a *
          vladimirov_kernel n z ((wickTemperedSpectralMeasureFamily m hm η C hC).p n α a)) =
      fun a => Φ a.1 (toChordMom a.1 a.2) := by
    ext a
    dsimp [wickTemperedSpectralMeasureFamily, Φ]
    ring
  rw [h_congr]
  change (∫ a : WickSpectralIndex n, Φ a.1 (toChordMom a.1 a.2) ∂(wickSpectralMeasure n)) = _
  rw [integral_wickSpectralMeasure hΦ_meas hΦ_int, wickMassShellH_eq_sum_integral]
  exact Finset.sum_congr rfl (fun P _ => integral_const_mul (η ^ P.cross) _)

theorem wickTemperedSpectralMeasureFamily_toSchwingerFamily {ι : Type*}
    (m : ℝ) (hm : 0 < m) (η : ℂ) (C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ)
    (hC : MassShellCoeffData m C) (n : ℕ) (α : Fin n → ι)
    {x : Fin n → Fin 4 → ℝ} (hx : x ∈ orderedEuclidN n) :
    (wickTemperedSpectralMeasureFamily m hm η C hC).toSchwingerFamily n α x =
      wickMassShellS m hm η C hC n α x :=
  wickTemperedSpectralMeasureFamily_H m hm η C hC n α (wickEmbedN_mem_forward_tube_n n hx)

theorem wickTemperedSpectralMeasureFamily_tubeCovariant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R.rep A (α i) (β i)) * C β q) :
    TubeCovariant R (wickTemperedSpectralMeasureFamily m hm η C hC).toTubeExtension := by
  intro n A z hz hAz α
  rw [TemperedForwardConeSpectralMeasureFamily.toTubeExtension_H,
      wickTemperedSpectralMeasureFamily_H m hm η C hC n α hAz]
  have h_cov := wickMassShellTubeCovariant R hm η hC hC_cov n A z hz hAz α
  rw [wickMassShellTubeExtension_H] at h_cov
  rw [h_cov]
  refine Finset.sum_congr rfl (fun β _ => congrArg (_ * ·) ?_)
  rw [TemperedForwardConeSpectralMeasureFamily.toTubeExtension_H,
      wickTemperedSpectralMeasureFamily_H m hm η C hC n β hz]

theorem wickTemperedSpectralMeasureFamily_tubePCT {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) {η : ℂ} (hη : η = 1 ∨ η = -1)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q) :
    TubePCT η R (wickTemperedSpectralMeasureFamily m hm η C hC).toTubeExtension := by
  intro n α z hz
  rw [TemperedForwardConeSpectralMeasureFamily.toTubeExtension_H,
      wickTemperedSpectralMeasureFamily_H m hm η C hC n α (neg_rev_mem_forward_tube_n n z hz)]
  have h_pct := wickMassShellTubePCT R hm hη hC hC_pct n α z hz
  rw [wickMassShellTubeExtension_H] at h_pct
  rw [h_pct]
  congr 1
  refine Finset.sum_congr rfl (fun β _ => congrArg (_ * ·) ?_)
  rw [TemperedForwardConeSpectralMeasureFamily.toTubeExtension_H,
      wickTemperedSpectralMeasureFamily_H m hm η C hC n (β ∘ Fin.rev) hz]

noncomputable def freeKGTemperedSpectralMeasureFamily {m : ℝ} (hm : 0 < m) :
    TemperedForwardConeSpectralMeasureFamily Unit :=
  wickTemperedSpectralMeasureFamily m hm 1 massiveKGCoeff (massiveKGCoeff_data hm)

noncomputable def freeDiracTemperedSpectralMeasureFamily {m : ℝ} (hm : 0 < m) :
    TemperedForwardConeSpectralMeasureFamily (Fin 2 ⊕ Fin 2) :=
  wickTemperedSpectralMeasureFamily m hm (-1) (diracMassShellCoeff m)
    (diracMassShellCoeff_data hm)

theorem vacFullEuclidOSAxioms {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) :
    FullEuclidOSAxioms R S η vacS where
  os0_smooth n _ := by
    cases n with
    | zero => exact contDiffOn_const
    | succ _ => exact contDiffOn_const
  os1_translation n _ _ _ _ := by
    cases n <;> rfl
  os1_rotation n _ _ α _ _ := by
    cases n with
    | zero =>
      have hα : α = Fin.elim0 := Subsingleton.elim _ _
      subst hα
      simp [vacS_zero]
    | succ _ =>
      simp [vacS_succ]
  os2_hermiticity := (vacOSAxioms R S η).os2_hermiticity
  os2_positivity := vacOSReflectionPositive S
  os3_permutation n π _ _ _ := by
    cases n with
    | zero =>
      have h0 : permInversions π = 0 := by
        unfold permInversions
        simp
      rw [h0, pow_zero, one_mul]
      rfl
    | succ _ =>
      simp [vacS_succ]

def vacForwardConeSpectralFamily (ι : Type*) : ForwardConeSpectralFamily ι where
  m
    | 0 => 1
    | _ + 1 => 0
  c
    | 0, _, _ => 1
    | _ + 1, _, k => Fin.elim0 k
  p
    | 0, _, _ => 0
    | _ + 1, _, k => Fin.elim0 k
  mem_forwardCone
    | 0, _, _ => zero_mem_forwardConeSpectralRegion 0
    | _ + 1, _, k => Fin.elim0 k

@[simp]
lemma vacForwardConeSpectralFamily_H (ι : Type*) :
    (vacForwardConeSpectralFamily ι).H = vacH := by
  ext n α z
  cases n with
  | zero =>
    change ∑ _k : Fin 1, (1 : ℂ) * vladimirov_kernel 0 z 0 = 1
    rw [Fin.sum_univ_one, vladimirov_kernel_zero_p_n, one_mul]
  | succ _ =>
    change ∑ k : Fin 0, _ = 0
    simp

@[simp]
lemma vacForwardConeSpectralFamily_toWightmanFamily (ι : Type*) :
    (vacForwardConeSpectralFamily ι).toWightmanFamily = vacW := by
  ext n α f
  rw [ForwardConeSpectralFamily.toWightmanFamily_apply]
  cases n with
  | zero =>
    change ∑ _k : Fin 1, (1 : ℂ) * minkowskiFourier f 0 = f 0
    rw [Fin.sum_univ_one, one_mul, minkowskiFourier_fin0]
  | succ _ =>
    change ∑ k : Fin 0, _ = 0
    simp

@[simp]
lemma vacForwardConeSpectralFamily_toSchwingerFamily (ι : Type*) :
    (vacForwardConeSpectralFamily ι).toSchwingerFamily = vacS := by
  ext n α x
  rw [ForwardConeSpectralFamily.toSchwingerFamily_apply, vacForwardConeSpectralFamily_H]
  cases n <;> rfl

noncomputable def vacOSReconstructionData {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) :
    OSReconstructionData (vacOSAxioms R S η) (vacOSTimeCluster R S) where
  m_spec := 1
  spec := vacSpectralDecomposition R S
  F := vacForwardConeSpectralFamily ι
  schwinger_eq n α x _ := by rw [vacForwardConeSpectralFamily_toSchwingerFamily]
  tube_covariant n A z hz hAz α := by
    change (vacForwardConeSpectralFamily ι).H n α (spinorPhi (A, sl2c_conj A) • z) =
      ∑ β : Fin n → ι, (∏ i, R.rep A (α i) (β i)) * (vacForwardConeSpectralFamily ι).H n β z
    simp_rw [vacForwardConeSpectralFamily_H]
    exact vacTubeCovariant R n A z hz hAz α
  tube_pct n α z hz := by
    change (vacForwardConeSpectralFamily ι).H n α (-(z ∘ Fin.rev)) =
      η ^ (n * (n - 1) / 2) * ∑ β : Fin n → ι,
        (∏ i, R.σ (-1, 1) (α i) (β i)) * (vacForwardConeSpectralFamily ι).H n (β ∘ Fin.rev) z
    simp_rw [vacForwardConeSpectralFamily_H]
    exact vacTubePCT R η n α z hz
  poincare := by
    rw [vacForwardConeSpectralFamily_toWightmanFamily]
    exact vacPoincareCovariant R
  weakLocality := by
    rw [vacForwardConeSpectralFamily_toWightmanFamily]
    exact vacWeakLocality η
  positivity := by
    rw [vacForwardConeSpectralFamily_toWightmanFamily]
    exact vacPositivity S

noncomputable def wickMassShellOSMeasureReconstructionData
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R_rep.rep A (α i) (β i)) * C β q)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R_rep.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q)
    (hOS : OSAxioms R_rep S η (wickMassShellS m hm η C hC))
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData) :
    OSMeasureReconstructionData hOS hcluster where
  Ω_spec := FockOmega M_mode.ν
  instMeasSpec := inferInstance
  spec := wickMassShellOSContinuousSpectralData hm M_mode hC hC_herm
    hOS.toReflectionPositiveData rfl
    (osContractionCondition_of_timeCluster hOS.toReflectionPositiveData
      hOS.os1_translation hcluster)
  F := wickTemperedSpectralMeasureFamily m hm η C hC
  schwinger_eq n α x hx :=
    (wickTemperedSpectralMeasureFamily_toSchwingerFamily m hm η C hC n α hx).symm
  tube_covariant := wickTemperedSpectralMeasureFamily_tubeCovariant R_rep hm η hC hC_cov
  tube_pct := wickTemperedSpectralMeasureFamily_tubePCT R_rep hm M_mode.hη hC hC_pct
  poincare := by
    rw [wickTemperedSpectralMeasureFamily_toWightmanFamily]
    exact wickMassShellPoincareCovariant R_rep hm η hC hC_cov
  weakLocality := by
    rw [wickTemperedSpectralMeasureFamily_toWightmanFamily]
    exact wickMassShellWeakLocality R_rep hm M_mode.hη hC hC_cov hC_pct
  positivity := by
    rw [wickTemperedSpectralMeasureFamily_toWightmanFamily]
    exact wickMassShellPositivity M_mode hC hC_herm

noncomputable def freeKGOSMeasureReconstructionData {m : ℝ} (hm : 0 < m) :
    OSMeasureReconstructionData (freeKGOSAxioms hm) (freeKGOSTimeCluster hm) :=
  wickMassShellOSMeasureReconstructionData hm (kgModeData hm) (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])
    (fun _ _ => by simp [massiveKGCoeff, trivialStarStructure])
    (fun _ _ => by simp [massiveKGCoeff, trivialRep])
    (freeKGOSAxioms hm) (freeKGOSTimeCluster hm)

noncomputable def freeDiracOSMeasureReconstructionData {m : ℝ} (hm : 0 < m) :
    OSMeasureReconstructionData (freeDiracOSAxioms hm) (freeDiracOSTimeCluster hm) :=
  wickMassShellOSMeasureReconstructionData hm (diracModeData hm) (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_lorentz m) (diracMassShellCoeff_herm m) (diracMassShellCoeff_pct m)
    (freeDiracOSAxioms hm) (freeDiracOSTimeCluster hm)

noncomputable def freeKGForwardConeOSEuclideanTubeBridge {m : ℝ} (hm : 0 < m) :
    ForwardConeOSEuclideanTubeBridge trivialRep trivialStarStructure 1 (freeKGS m hm) :=
  (freeKGOSMeasureReconstructionData hm).toForwardConeOSEuclideanTubeBridge

noncomputable def freeKGForwardConeOSReconstructedWightman {m : ℝ} (hm : 0 < m) :
    ForwardConeOSReconstructedWightman trivialRep trivialStarStructure 1 (freeKGS m hm) :=
  (freeKGOSMeasureReconstructionData hm).toForwardConeOSReconstructedWightman

noncomputable def freeDiracForwardConeOSEuclideanTubeBridge {m : ℝ} (hm : 0 < m) :
    ForwardConeOSEuclideanTubeBridge diracRep diracStarStructure (-1) (freeDiracS m hm) :=
  (freeDiracOSMeasureReconstructionData hm).toForwardConeOSEuclideanTubeBridge

noncomputable def freeDiracForwardConeOSReconstructedWightman {m : ℝ} (hm : 0 < m) :
    ForwardConeOSReconstructedWightman diracRep diracStarStructure (-1) (freeDiracS m hm) :=
  (freeDiracOSMeasureReconstructionData hm).toForwardConeOSReconstructedWightman

noncomputable def wickMassShellWightmanAxioms
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R_rep : HolomorphicLorentzRep ι) (S : StarStructure R_rep)
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R_rep.rep A (α i) (β i)) * C β q)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R_rep.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q) :
    WightmanAxioms R_rep S η where
  WData := wightmanPositiveDataOfPositivity S (wickMassShellW m η C hC)
    (wickMassShellPositivity M_mode hC hC_herm)
  E := wickMassShellTubeExtension m hm η C hC
  positivity := wickMassShellPositivity M_mode hC hC_herm
  poincare := wickMassShellPoincareCovariant R_rep hm η hC hC_cov
  spectrum := wickMassShell_forwardConeSpectrumCondition hm η hC
  weakLocality := wickMassShellWeakLocality R_rep hm M_mode.hη hC hC_cov hC_pct
  tube_covariant := wickMassShellTubeCovariant R_rep hm η hC hC_cov
  tube_pct := wickMassShellTubePCT R_rep hm M_mode.hη hC hC_pct
  cyclic := wightmanVacuumCyclic _

noncomputable def wickMassShellWightmanAxiomsWithUniqueVacuum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R_rep : HolomorphicLorentzRep ι) (S : StarStructure R_rep)
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R_rep.rep A (α i) (β i)) * C β q)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R_rep.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q) :
    WightmanAxiomsWithUniqueVacuum R_rep S η where
  toWightmanAxioms :=
    wickMassShellWightmanAxioms R_rep S hm M_mode hC hC_cov hC_herm hC_pct
  vacuumNormalized := wickMassShellWightmanVacuumNormalized M_mode hC hC_herm
  cluster _ ha := wickMassShellWightmanClusterAlong hm M_mode hC hC_herm _ rfl ha
  vacuumUnique := wickMassShellWightmanVacuumUnique hm M_mode hC hC_herm _ rfl _

noncomputable def freeKGWightmanAxioms {m : ℝ} (hm : 0 < m) :
    WightmanAxioms trivialRep trivialStarStructure 1 :=
  wickMassShellWightmanAxioms trivialRep trivialStarStructure hm (kgModeData hm)
    (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])
    (fun _ _ => by simp [massiveKGCoeff, trivialStarStructure])
    (fun _ _ => by simp [massiveKGCoeff, trivialRep])

noncomputable def freeDiracWightmanAxioms {m : ℝ} (hm : 0 < m) :
    WightmanAxioms diracRep diracStarStructure (-1) :=
  wickMassShellWightmanAxioms diracRep diracStarStructure hm (diracModeData hm)
    (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_lorentz m) (diracMassShellCoeff_herm m) (diracMassShellCoeff_pct m)

noncomputable def freeKGWightmanAxiomsWithUniqueVacuum {m : ℝ} (hm : 0 < m) :
    WightmanAxiomsWithUniqueVacuum trivialRep trivialStarStructure 1 :=
  wickMassShellWightmanAxiomsWithUniqueVacuum trivialRep trivialStarStructure hm
    (kgModeData hm) (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])
    (fun _ _ => by simp [massiveKGCoeff, trivialStarStructure])
    (fun _ _ => by simp [massiveKGCoeff, trivialRep])

noncomputable def freeDiracWightmanAxiomsWithUniqueVacuum {m : ℝ} (hm : 0 < m) :
    WightmanAxiomsWithUniqueVacuum diracRep diracStarStructure (-1) :=
  wickMassShellWightmanAxiomsWithUniqueVacuum diracRep diracStarStructure hm
    (diracModeData hm) (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_lorentz m) (diracMassShellCoeff_herm m) (diracMassShellCoeff_pct m)

theorem freeKGClusterAlong {m : ℝ} (hm : 0 < m) {a : Fin 4 → ℝ} (ha : a ≠ 0) :
    WightmanClusterAlong (freeKGWightmanAxioms hm).WData a :=
  (freeKGWightmanAxiomsWithUniqueVacuum hm).cluster a ha

theorem freeDiracClusterAlong {m : ℝ} (hm : 0 < m) {a : Fin 4 → ℝ} (ha : a ≠ 0) :
    WightmanClusterAlong (freeDiracWightmanAxioms hm).WData a :=
  (freeDiracWightmanAxiomsWithUniqueVacuum hm).cluster a ha

theorem freeKGVacuumUnique {m : ℝ} (hm : 0 < m) :
    WightmanVacuumUnique (freeKGWightmanAxioms hm).WData
      (freeKGWightmanAxioms hm).translationInvariant :=
  (freeKGWightmanAxiomsWithUniqueVacuum hm).vacuumUnique

theorem freeDiracVacuumUnique {m : ℝ} (hm : 0 < m) :
    WightmanVacuumUnique (freeDiracWightmanAxioms hm).WData
      (freeDiracWightmanAxioms hm).translationInvariant :=
  (freeDiracWightmanAxiomsWithUniqueVacuum hm).vacuumUnique

theorem freeKGWightmanVacuumNormalized {m : ℝ} (hm : 0 < m) :
    WightmanVacuumNormalized trivialStarStructure (freeKGW m hm) :=
  (freeKGWightmanAxiomsWithUniqueVacuum hm).vacuumNormalized

theorem freeDiracWightmanVacuumNormalized {m : ℝ} (hm : 0 < m) :
    WightmanVacuumNormalized diracStarStructure (freeDiracW m hm) :=
  (freeDiracWightmanAxiomsWithUniqueVacuum hm).vacuumNormalized

theorem freeKGOSVacuumNormalized {m : ℝ} (hm : 0 < m) :
    OSVacuumNormalized (freeKGS m hm) :=
  wickMassShellS_vacuumNormalized m hm 1 massiveKGCoeff (massiveKGCoeff_data hm)

theorem freeDiracOSVacuumNormalized {m : ℝ} (hm : 0 < m) :
    OSVacuumNormalized (freeDiracS m hm) :=
  wickMassShellS_vacuumNormalized m hm (-1) (diracMassShellCoeff m) (diracMassShellCoeff_data hm)

theorem freeKGOS_exponential_cluster {m : ℝ} (hm : 0 < m) {τ : ℝ} (hτ : 0 ≤ τ)
    (A B : OSConfig Unit) :
    ‖osKernel trivialStarStructure (freeKGS m hm) A (osConfigTimeShift τ hτ B) -
        osKernel trivialStarStructure (freeKGS m hm) A (osVacuumConfig Unit) *
          osKernel trivialStarStructure (freeKGS m hm) (osVacuumConfig Unit) B‖ ≤
      ‖fockOSMap hm (kgModeData hm) (massiveKGCoeff_data hm) A‖ *
        ‖fockOSMap hm (kgModeData hm) (massiveKGCoeff_data hm) B‖ *
          Real.exp (-(m * τ)) :=
  wickMassShellOS_exponential_cluster hm (kgModeData hm) (massiveKGCoeff_data hm)
    (fun _ _ => by simp [massiveKGCoeff, trivialStarStructure]) hτ A B

theorem freeDiracOS_exponential_cluster {m : ℝ} (hm : 0 < m) {τ : ℝ} (hτ : 0 ≤ τ)
    (A B : OSConfig (Fin 2 ⊕ Fin 2)) :
    ‖osKernel diracStarStructure (freeDiracS m hm) A (osConfigTimeShift τ hτ B) -
        osKernel diracStarStructure (freeDiracS m hm) A (osVacuumConfig (Fin 2 ⊕ Fin 2)) *
          osKernel diracStarStructure (freeDiracS m hm) (osVacuumConfig (Fin 2 ⊕ Fin 2)) B‖ ≤
      ‖fockOSMap hm (diracModeData hm) (diracMassShellCoeff_data hm) A‖ *
        ‖fockOSMap hm (diracModeData hm) (diracMassShellCoeff_data hm) B‖ *
          Real.exp (-(m * τ)) :=
  wickMassShellOS_exponential_cluster hm (diracModeData hm) (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_herm m) hτ A B

theorem freeKG_grand_master {m : ℝ} (hm : 0 < m) :
    OSAxioms trivialRep trivialStarStructure 1 (freeKGS m hm) ∧
    OSVacuumNormalized (freeKGS m hm) ∧
    (∀ {τ : ℝ} (hτ : 0 ≤ τ) (A B : OSConfig Unit),
      ‖osKernel trivialStarStructure (freeKGS m hm) A (osConfigTimeShift τ hτ B) -
          osKernel trivialStarStructure (freeKGS m hm) A (osVacuumConfig Unit) *
            osKernel trivialStarStructure (freeKGS m hm) (osVacuumConfig Unit) B‖ ≤
        ‖fockOSMap hm (kgModeData hm) (massiveKGCoeff_data hm) A‖ *
          ‖fockOSMap hm (kgModeData hm) (massiveKGCoeff_data hm) B‖ *
            Real.exp (-(m * τ))) ∧
    (freeKGOSHolomorphicSemigroup hm).IsWeaklyHolomorphic ∧
    (freeKGForwardConeOSReconstructedWightman hm).W = freeKGW m hm ∧
    Positivity trivialStarStructure (freeKGW m hm) ∧
    PoincareCovariant trivialRep (freeKGW m hm) ∧
    ForwardConeSpectrumCondition (freeKGW m hm) ∧
    WeakLocality 1 (freeKGW m hm) ∧
    WightmanPCT 1 trivialRep (freeKGW m hm) ∧
    WightmanVacuumNormalized trivialStarStructure (freeKGW m hm) ∧
    (∀ {a : Fin 4 → ℝ}, a ≠ 0 → WightmanClusterAlong (freeKGWightmanAxioms hm).WData a) ∧
    WightmanVacuumUnique (freeKGWightmanAxioms hm).WData
      (freeKGWightmanAxioms hm).translationInvariant ∧
    (∀ {η : ℂ}, WeakLocality η (freeKGW m hm) → η = 1) ∧
    freeKGW m hm 2 default ≠ 0 ∧
    ¬ ZeroMomentumSpectrumCondition (freeKGW m hm) := by
  refine ⟨freeKGOSAxioms hm,
    freeKGOSVacuumNormalized hm,
    fun hτ A B => freeKGOS_exponential_cluster hm hτ A B,
    freeKGOSHolomorphicSemigroup_isWeaklyHolomorphic hm,
    ?_,
    freeKGPositivity hm,
    freeKGPoincareCovariant hm,
    freeKG_forwardConeSpectrumCondition hm,
    freeKGWeakLocality hm,
    freeKGWightmanPCT hm,
    freeKGWightmanVacuumNormalized hm,
    fun ha => freeKGClusterAlong hm ha,
    freeKGVacuumUnique hm,
    fun hloc => freeKG_spin_statistics hm hloc,
    freeKGW_twoPoint_ne_zero hm,
    not_zeroMomentumSpectrumCondition_freeKGW hm⟩
  unfold freeKGForwardConeOSReconstructedWightman
  rw [OSMeasureReconstructionData.toForwardConeOSReconstructedWightman_W]
  exact wickTemperedSpectralMeasureFamily_toWightmanFamily m hm 1 massiveKGCoeff
    (massiveKGCoeff_data hm)

theorem freeDirac_grand_master {m : ℝ} (hm : 0 < m) :
    OSAxioms diracRep diracStarStructure (-1) (freeDiracS m hm) ∧
    OSVacuumNormalized (freeDiracS m hm) ∧
    (∀ {τ : ℝ} (hτ : 0 ≤ τ) (A B : OSConfig (Fin 2 ⊕ Fin 2)),
      ‖osKernel diracStarStructure (freeDiracS m hm) A (osConfigTimeShift τ hτ B) -
          osKernel diracStarStructure (freeDiracS m hm) A (osVacuumConfig (Fin 2 ⊕ Fin 2)) *
            osKernel diracStarStructure (freeDiracS m hm) (osVacuumConfig (Fin 2 ⊕ Fin 2)) B‖ ≤
        ‖fockOSMap hm (diracModeData hm) (diracMassShellCoeff_data hm) A‖ *
          ‖fockOSMap hm (diracModeData hm) (diracMassShellCoeff_data hm) B‖ *
            Real.exp (-(m * τ))) ∧
    (freeDiracOSHolomorphicSemigroup hm).IsWeaklyHolomorphic ∧
    (freeDiracForwardConeOSReconstructedWightman hm).W = freeDiracW m hm ∧
    Positivity diracStarStructure (freeDiracW m hm) ∧
    PoincareCovariant diracRep (freeDiracW m hm) ∧
    ForwardConeSpectrumCondition (freeDiracW m hm) ∧
    WeakLocality (-1) (freeDiracW m hm) ∧
    WightmanPCT (-1) diracRep (freeDiracW m hm) ∧
    WightmanVacuumNormalized diracStarStructure (freeDiracW m hm) ∧
    (∀ {a : Fin 4 → ℝ}, a ≠ 0 → WightmanClusterAlong (freeDiracWightmanAxioms hm).WData a) ∧
    WightmanVacuumUnique (freeDiracWightmanAxioms hm).WData
      (freeDiracWightmanAxioms hm).translationInvariant ∧
    (∀ {η : ℂ}, WeakLocality η (freeDiracW m hm) → η = -1) ∧
    (∃ β : Fin 2 → Fin 2 ⊕ Fin 2, freeDiracW m hm 2 β ≠ 0) ∧
    ¬ ZeroMomentumSpectrumCondition (freeDiracW m hm) := by
  refine ⟨freeDiracOSAxioms hm,
    freeDiracOSVacuumNormalized hm,
    fun hτ A B => freeDiracOS_exponential_cluster hm hτ A B,
    freeDiracOSHolomorphicSemigroup_isWeaklyHolomorphic hm,
    ?_,
    freeDiracPositivity hm,
    freeDiracPoincareCovariant hm,
    freeDirac_forwardConeSpectrumCondition hm,
    freeDiracWeakLocality hm,
    freeDiracWightmanPCT hm,
    freeDiracWightmanVacuumNormalized hm,
    fun ha => freeDiracClusterAlong hm ha,
    freeDiracVacuumUnique hm,
    fun hloc => freeDirac_spin_statistics hm hloc,
    freeDiracW_twoPoint_nondegenerate hm,
    not_zeroMomentumSpectrumCondition_freeDiracW hm⟩
  unfold freeDiracForwardConeOSReconstructedWightman
  rw [OSMeasureReconstructionData.toForwardConeOSReconstructedWightman_W]
  exact wickTemperedSpectralMeasureFamily_toWightmanFamily m hm (-1) (diracMassShellCoeff m)
    (diracMassShellCoeff_data hm)

end

end QFT
