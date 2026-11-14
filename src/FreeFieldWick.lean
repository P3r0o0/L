import Mathlib.MeasureTheory.Integral.Pi
import WickCombinatorics
import VacuumTheory

open scoped ComplexConjugate Topology BigOperators Matrix
open Geometry Geometry.MatrixAnalysis MeasureTheory Filter Complex Matrix

namespace QFT

noncomputable section

lemma forward_light_cone_add {x y : Fin 4 → ℝ}
    (hx : x ∈ forward_light_cone) (hy : y ∈ forward_light_cone) :
    x + y ∈ forward_light_cone := by
  have hx_cl : x ∈ closed_forward_light_cone := ⟨hx.1.le, hx.2.le⟩
  have hy_cl : y ∈ closed_forward_light_cone := ⟨hy.1.le, hy.2.le⟩
  have hxy : 0 ≤ minkowskiInner x y := closed_forward_light_cone_inner_nonneg hx_cl hy_cl
  refine ⟨add_pos hx.1 hy.1, ?_⟩
  have h_eq : minkowskiInner (x + y) (x + y) =
      minkowskiInner x x + minkowskiInner y y + 2 * minkowskiInner x y := by
    simp only [minkowskiInner_explicit, Pi.add_apply]
    ring
  rw [h_eq]
  linarith [hx.2, hy.2]

lemma add_mem_closure_forward_light_cone {x y : Fin 4 → ℝ}
    (hx : x ∈ closure forward_light_cone) (hy : y ∈ closure forward_light_cone) :
    x + y ∈ closure forward_light_cone := by
  rw [closure_forward_light_cone_eq] at hx hy ⊢
  have hxy : 0 ≤ minkowskiInner x y := closed_forward_light_cone_inner_nonneg hx hy
  refine ⟨add_nonneg hx.1 hy.1, ?_⟩
  have h_eq : minkowskiInner (x + y) (x + y) =
      minkowskiInner x x + minkowskiInner y y + 2 * minkowskiInner x y := by
    simp only [minkowskiInner_explicit, Pi.add_apply]
    ring
  rw [h_eq]
  linarith [hx.2, hy.2]

lemma sum_mem_closure_forward_light_cone {α : Type*} (s : Finset α) (f : α → Fin 4 → ℝ)
    (hf : ∀ a ∈ s, f a ∈ closure forward_light_cone) :
    (∑ a ∈ s, f a) ∈ closure forward_light_cone := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      exact zero_mem_closure_forward_light_cone
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact add_mem_closure_forward_light_cone
        (hf a (Finset.mem_insert_self a s))
        (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

lemma add_mem_forwardConeSpectralRegion {n : ℕ} {p₁ p₂ : Fin n → Fin 4 → ℝ}
    (hp₁ : p₁ ∈ forwardConeSpectralRegion n) (hp₂ : p₂ ∈ forwardConeSpectralRegion n) :
    p₁ + p₂ ∈ forwardConeSpectralRegion n := by
  refine ⟨?_, fun k => ?_⟩
  · simp only [Pi.add_apply, Finset.sum_add_distrib, hp₁.1, hp₂.1, add_zero]
  · simp only [Pi.add_apply, Finset.sum_add_distrib]
    exact add_mem_closure_forward_light_cone (hp₁.2 k) (hp₂.2 k)

lemma sum_mem_forwardConeSpectralRegion {α : Type*} {n : ℕ} (s : Finset α)
    (f : α → Fin n → Fin 4 → ℝ)
    (hf : ∀ a ∈ s, f a ∈ forwardConeSpectralRegion n) :
    (∑ a ∈ s, f a) ∈ forwardConeSpectralRegion n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      exact zero_mem_forwardConeSpectralRegion n
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact add_mem_forwardConeSpectralRegion
        (hf a (Finset.mem_insert_self a s))
        (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

lemma im_sub_mem_forward_light_cone_aux {n : ℕ} {z : Fin n → Fin 4 → ℂ}
    (hz : z ∈ forward_tube_n n) :
    ∀ (d u : ℕ) (hv : u + (d + 1) < n),
      (fun μ => (z ⟨u + (d + 1), hv⟩ μ).im - (z ⟨u, by omega⟩ μ).im) ∈ forward_light_cone
  | 0, u, hv => by
      have h0 := diff_im_mem_forward_cone n z hz ⟨u, by omega⟩ hv
      convert h0 using 1
      ext μ
      simp [diff_im, diff_z]
  | d + 1, u, hv => by
      have h1 := im_sub_mem_forward_light_cone_aux hz d u (by omega)
      have h2 := diff_im_mem_forward_cone n z hz ⟨u + (d + 1), by omega⟩ hv
      have h_eq :
          (fun μ => (z ⟨u + (d + 1 + 1), hv⟩ μ).im - (z ⟨u, by omega⟩ μ).im) =
          (fun μ => (z ⟨u + (d + 1), by omega⟩ μ).im - (z ⟨u, by omega⟩ μ).im) +
            diff_im n z ⟨u + (d + 1), by omega⟩ hv := by
        ext μ
        have hidx : (⟨u + (d + 1 + 1), hv⟩ : Fin n) = ⟨u + (d + 1) + 1, hv⟩ := rfl
        rw [hidx]
        dsimp only [diff_im, diff_z, Pi.add_apply]
        rw [Pi.sub_apply, sub_im]
        ring
      rw [h_eq]
      exact forward_light_cone_add h1 h2

lemma pair_mem_forward_tube_two {n : ℕ} {z : Fin n → Fin 4 → ℂ}
    (hz : z ∈ forward_tube_n n) {u v : Fin n} (huv : u < v) :
    ![z u, z v] ∈ forward_tube_n 2 := by
  intro i hi
  have hi0 : i = 0 := by omega
  subst hi0
  have hv_eq : u.val + ((v.val - u.val - 1) + 1) = v.val := by
    have hlt : u.val < v.val := huv
    omega
  have hv_lt : u.val + ((v.val - u.val - 1) + 1) < n := by
    rw [hv_eq]
    exact v.isLt
  have h_cone := im_sub_mem_forward_light_cone_aux hz (v.val - u.val - 1) u.val hv_lt
  have hu_fin : (⟨u.val, by omega⟩ : Fin n) = u := Fin.ext rfl
  have hv_fin : (⟨u.val + ((v.val - u.val - 1) + 1), hv_lt⟩ : Fin n) = v := Fin.ext hv_eq
  convert h_cone using 1
  ext μ
  simp [hu_fin, hv_fin]

def pairProjCLM {n : ℕ} (u v : Fin n) :
    (Fin n → Fin 4 → ℂ) →L[ℂ] (Fin 2 → Fin 4 → ℂ) :=
  ContinuousLinearMap.pi
    ![ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => Fin 4 → ℂ) u,
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => Fin 4 → ℂ) v]

@[simp]
lemma pairProjCLM_apply {n : ℕ} (u v : Fin n) (z : Fin n → Fin 4 → ℂ) :
    pairProjCLM u v z = ![z u, z v] := by
  ext s μ
  fin_cases s <;> rfl

def chordTwoPointMomentum {n : ℕ} (P : ChordPairing n) (c : P.Chord) (q : Fin 4 → ℝ) :
    Fin n → Fin 4 → ℝ :=
  fun i => if i = c.1 then q else if i = P.mate c.1 then -q else 0

lemma sum_chordTwoPointMomentum {n : ℕ} (P : ChordPairing n) (c : P.Chord) (q : Fin 4 → ℝ) :
    ∑ i : Fin n, chordTwoPointMomentum P c q i = 0 := by
  have hne : c.1 ≠ P.mate c.1 := ne_of_lt c.2
  rw [P.sum_univ_eq_sum_chord]
  have h_term : ∀ c' : P.Chord,
      chordTwoPointMomentum P c q c'.1 + chordTwoPointMomentum P c q (P.mate c'.1) = 0 := by
    intro c'
    by_cases hcc : c' = c
    · subst hcc
      dsimp [chordTwoPointMomentum]
      rw [if_pos rfl, if_neg hne.symm, if_pos rfl, add_neg_cancel]
    · have h1 : c'.1 ≠ c.1 := fun h => hcc (Subtype.ext h)
      have h2 : c'.1 ≠ P.mate c.1 := by
        intro h
        have hlt : P.mate c.1 < P.mate (P.mate c.1) := by simpa [h] using c'.2
        rw [P.mate_mate] at hlt
        exact not_lt_of_gt c.2 hlt
      have h3 : P.mate c'.1 ≠ c.1 := by
        intro h
        have hm := congrArg P.mate h
        rw [P.mate_mate] at hm
        exact h2 hm
      have h4 : P.mate c'.1 ≠ P.mate c.1 := fun h => h1 (P.mate.injective h)
      dsimp [chordTwoPointMomentum]
      rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, add_zero]
  simp_rw [h_term, Finset.sum_const_zero]

lemma partial_sum_chordTwoPointMomentum {n : ℕ} (P : ChordPairing n) (c : P.Chord)
    (q : Fin 4 → ℝ) (k : Fin n) :
    (∑ i ∈ Finset.univ.filter (· ≤ k), chordTwoPointMomentum P c q i) =
      if c.1 ≤ k ∧ k < P.mate c.1 then q else 0 := by
  have hne : c.1 ≠ P.mate c.1 := ne_of_lt c.2
  have h_split :
      ∀ i : Fin n, chordTwoPointMomentum P c q i =
        (if i = c.1 then q else 0) + (if i = P.mate c.1 then -q else 0) := by
    intro i
    dsimp only [chordTwoPointMomentum]
    by_cases h1 : i = c.1
    · subst h1
      simp [hne]
    · simp [h1]
  simp_rw [h_split]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h1 : c.1 ≤ k
  · by_cases h2 : P.mate c.1 ≤ k
    · have hnot : ¬ k < P.mate c.1 := not_lt_of_ge h2
      simp [h1, h2, hnot]
    · have hlt : k < P.mate c.1 := lt_of_not_ge h2
      simp [h1, h2, hlt]
  · have h2 : ¬ P.mate c.1 ≤ k := fun hm => h1 (c.2.le.trans hm)
    simp [h1, h2]

lemma chordTwoPointMomentum_mem_forwardConeSpectralRegion {n : ℕ} (P : ChordPairing n)
    (c : P.Chord) {q : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone) :
    chordTwoPointMomentum P c q ∈ forwardConeSpectralRegion n := by
  refine ⟨sum_chordTwoPointMomentum P c q, fun k => ?_⟩
  rw [partial_sum_chordTwoPointMomentum]
  split_ifs
  · exact hq
  · exact zero_mem_closure_forward_light_cone

namespace ChordPairing

noncomputable def momentum {n : ℕ} (m : ℝ) (P : ChordPairing n)
    (p : P.Chord → Fin 3 → ℝ) : Fin n → Fin 4 → ℝ :=
  fun i => ∑ c : P.Chord, chordTwoPointMomentum P c (massShellVec m (p c)) i

lemma momentum_eq_sum {n : ℕ} (m : ℝ) (P : ChordPairing n)
    (p : P.Chord → Fin 3 → ℝ) :
    P.momentum m p = ∑ c : P.Chord, chordTwoPointMomentum P c (massShellVec m (p c)) := by
  ext i μ
  simp [momentum, Finset.sum_apply]

@[simp]
lemma momentum_apply_fst {n : ℕ} (m : ℝ) (P : ChordPairing n)
    (p : P.Chord → Fin 3 → ℝ) (c : P.Chord) :
    P.momentum m p c.1 = massShellVec m (p c) := by
  dsimp [momentum]
  have h_eq : ∀ c' : P.Chord,
      chordTwoPointMomentum P c' (massShellVec m (p c')) c.1 =
        if c' = c then massShellVec m (p c) else 0 := by
    intro c'
    by_cases hcc : c' = c
    · subst hcc
      simp [chordTwoPointMomentum]
    · have h1 : c.1 ≠ c'.1 := fun h => hcc (Subtype.ext h.symm)
      have h2 : c.1 ≠ P.mate c'.1 := by
        intro h
        have hlt : P.mate c'.1 < P.mate (P.mate c'.1) := by simpa [h] using c.2
        rw [P.mate_mate] at hlt
        exact not_lt_of_gt c'.2 hlt
      simp [chordTwoPointMomentum, h1, h2, hcc]
  simp_rw [h_eq]
  simp

@[simp]
lemma momentum_apply_mate {n : ℕ} (m : ℝ) (P : ChordPairing n)
    (p : P.Chord → Fin 3 → ℝ) (c : P.Chord) :
    P.momentum m p (P.mate c.1) = -massShellVec m (p c) := by
  dsimp [momentum]
  have h_eq : ∀ c' : P.Chord,
      chordTwoPointMomentum P c' (massShellVec m (p c')) (P.mate c.1) =
        if c' = c then -massShellVec m (p c) else 0 := by
    intro c'
    by_cases hcc : c' = c
    · subst hcc
      have hne : P.mate c'.1 ≠ c'.1 := (ne_of_lt c'.2).symm
      simp [chordTwoPointMomentum, hne]
    · have h1 : P.mate c.1 ≠ c'.1 := by
        intro h
        have hlt : P.mate c.1 < P.mate (P.mate c.1) := by simpa [← h] using c'.2
        rw [P.mate_mate] at hlt
        exact not_lt_of_gt c.2 hlt
      have h2 : P.mate c.1 ≠ P.mate c'.1 := fun h => hcc (Subtype.ext (P.mate.injective h.symm))
      simp [chordTwoPointMomentum, h1, h2, hcc]
  simp_rw [h_eq]
  simp

lemma momentum_mem_forwardConeSpectralRegion {n : ℕ} {m : ℝ} (hm : 0 < m)
    (P : ChordPairing n) (p : P.Chord → Fin 3 → ℝ) :
    P.momentum m p ∈ forwardConeSpectralRegion n := by
  rw [P.momentum_eq_sum]
  exact sum_mem_forwardConeSpectralRegion Finset.univ _ (fun c _ =>
    chordTwoPointMomentum_mem_forwardConeSpectralRegion P c
      (massShellVec_mem_closure_forward_light_cone hm (p c)))

lemma continuous_momentum {n : ℕ} (m : ℝ) (P : ChordPairing n) :
    Continuous (P.momentum m) := by
  refine continuous_pi (fun i => continuous_finsetSum Finset.univ (fun c _ => ?_))
  dsimp [chordTwoPointMomentum]
  split_ifs
  · exact (continuous_massShellVec m).comp (continuous_apply c)
  · exact ((continuous_massShellVec m).comp (continuous_apply c)).neg
  · exact continuous_const

lemma measurable_momentum {n : ℕ} (m : ℝ) (P : ChordPairing n) :
    Measurable (P.momentum m) :=
  (P.continuous_momentum m).measurable

lemma vladimirov_kernel_momentum {n : ℕ} (m : ℝ) (P : ChordPairing n)
    (z : Fin n → Fin 4 → ℂ) (p : P.Chord → Fin 3 → ℝ) :
    vladimirov_kernel n z (P.momentum m p) =
      ∏ c : P.Chord, vladimirov_kernel 2 ![z c.1, z (P.mate c.1)]
        (twoPointMomentum (massShellVec m (p c))) := by
  unfold vladimirov_kernel
  rw [P.sum_univ_eq_sum_chord, Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl (fun c _ => ?_)
  congr 1
  rw [Fin.sum_univ_two, P.momentum_apply_fst, P.momentum_apply_mate]
  simp only [Fin.isValue, twoPointMomentum_zero, twoPointMomentum_one,
    Matrix.cons_val_zero, Matrix.cons_val_one]

lemma one_add_norm_chord_le_momentumToEuclid {n : ℕ} (m : ℝ) (P : ChordPairing n)
    (p : P.Chord → Fin 3 → ℝ) (c : P.Chord) :
    1 + ‖p c‖ ≤
      (2 * Real.pi) * (1 + ‖momentumToEuclidCLMN n (P.momentum m p)‖) := by
  let u := momentumToEuclidCLMN n (P.momentum m p)
  have hpi : 0 < 2 * Real.pi := by positivity
  have hp_norm : ‖p c‖ ≤ (2 * Real.pi) * ‖u‖ := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hpi.le (norm_nonneg u))).mpr (fun j => ?_)
    have hu_coord : u (c.1, j.succ) = (2 * Real.pi)⁻¹ * p c j := by
      have hm := P.momentum_apply_fst m p c
      have hu_app : u (c.1, j.succ) = (2 * Real.pi)⁻¹ * P.momentum m p c.1 j.succ := by
        dsimp only [u, momentumToEuclidCLMN, posScaledMomentumCLMN, posScaledMomentumN,
          piSpaceEquiv, finCurryEquiv, finEuclidEquiv]
        simp
      rw [hu_app, hm]
      fin_cases j <;> simp [massShellVec]
    have hpj : p c j = (2 * Real.pi) * u (c.1, j.succ) := by
      rw [hu_coord]
      field_simp [hpi.ne']
    calc ‖p c j‖ = ‖(2 * Real.pi) * u (c.1, j.succ)‖ := by rw [hpj]
      _ = (2 * Real.pi) * ‖u (c.1, j.succ)‖ := by
          rw [norm_mul, Real.norm_of_nonneg hpi.le]
      _ ≤ (2 * Real.pi) * ‖u‖ :=
          mul_le_mul_of_nonneg_left (PiLp.norm_apply_le u (c.1, j.succ)) hpi.le
  have hpi1 : 1 ≤ 2 * Real.pi := by
    have := Real.pi_gt_three
    linarith
  linarith

theorem norm_schwartz_momentumToEuclid_chord_le {n : ℕ} (m : ℝ) (P : ChordPairing n)
    (g : SchwartzMap (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ) (p : P.Chord → Fin 3 → ℝ) :
    ‖g (momentumToEuclidCLMN n (P.momentum m p))‖ ≤
      ((4 * Real.pi) ^ (4 * Fintype.card P.Chord) *
        ((Finset.Iic (4 * Fintype.card P.Chord, 0)).sup
          (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ) g)) *
        ∏ c : P.Chord, ((1 + ‖p c‖) ^ 4)⁻¹ := by
  let k := Fintype.card P.Chord
  let u := momentumToEuclidCLMN n (P.momentum m p)
  let S : ℝ := (Finset.Iic (4 * k, 0)).sup
    (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ) g
  have h_sch : (1 + ‖u‖) ^ (4 * k) * ‖g u‖ ≤ 2 ^ (4 * k) * S := by
    have h0 := SchwartzMap.one_add_le_sup_seminorm_apply
      (𝕜 := ℂ) (m := (4 * k, 0)) (k := 4 * k) (n := 0) le_rfl le_rfl g u
    have h_fam :
        (fun m : ℕ × ℕ =>
          SchwartzMap.seminorm (E := EuclideanSpace ℝ (Fin n × Fin 4)) (F := ℂ) ℂ m.1 m.2) =
        schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ := rfl
    simpa [norm_iteratedFDeriv_zero, h_fam, S] using h0
  have h_prod_p :
      (∏ c : P.Chord, (1 + ‖p c‖) ^ 4) ≤ (2 * Real.pi) ^ (4 * k) * (1 + ‖u‖) ^ (4 * k) := by
    have h_each : ∀ c : P.Chord, (1 + ‖p c‖) ^ 4 ≤ ((2 * Real.pi) * (1 + ‖u‖)) ^ 4 :=
      fun c => pow_le_pow_left₀ (by positivity)
        (P.one_add_norm_chord_le_momentumToEuclid m p c) 4
    calc (∏ c : P.Chord, (1 + ‖p c‖) ^ 4)
        ≤ ∏ _c : P.Chord, ((2 * Real.pi) * (1 + ‖u‖)) ^ 4 :=
          Finset.prod_le_prod (fun _ _ => by positivity) (fun c _ => h_each c)
      _ = (((2 * Real.pi) * (1 + ‖u‖)) ^ 4) ^ k := by
          rw [Finset.prod_const, Finset.card_univ]
      _ = ((2 * Real.pi) * (1 + ‖u‖)) ^ (4 * k) := (pow_mul _ 4 k).symm
      _ = (2 * Real.pi) ^ (4 * k) * (1 + ‖u‖) ^ (4 * k) := mul_pow _ _ (4 * k)
  have h_prod :
      (∏ c : P.Chord, (1 + ‖p c‖) ^ 4) * ‖g u‖ ≤ (4 * Real.pi) ^ (4 * k) * S := by
    calc (∏ c : P.Chord, (1 + ‖p c‖) ^ 4) * ‖g u‖
        ≤ ((2 * Real.pi) ^ (4 * k) * (1 + ‖u‖) ^ (4 * k)) * ‖g u‖ :=
          mul_le_mul_of_nonneg_right h_prod_p (norm_nonneg _)
      _ = (2 * Real.pi) ^ (4 * k) * ((1 + ‖u‖) ^ (4 * k) * ‖g u‖) := by ring
      _ ≤ (2 * Real.pi) ^ (4 * k) * (2 ^ (4 * k) * S) :=
          mul_le_mul_of_nonneg_left h_sch (by positivity)
      _ = ((2 * Real.pi) * 2) ^ (4 * k) * S := by rw [← mul_assoc, ← mul_pow]
      _ = (4 * Real.pi) ^ (4 * k) * S := by
          congr 2
          ring
  have h_pos : 0 < ∏ c : P.Chord, (1 + ‖p c‖) ^ 4 :=
    Finset.prod_pos (fun _ _ => by positivity)
  rw [Finset.prod_inv_distrib]
  exact (le_mul_inv_iff₀' h_pos).mpr h_prod

end ChordPairing

noncomputable def wickChordWeight {κ : Type*} {n : ℕ} (m : ℝ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (P : ChordPairing n) (α : Fin n → κ)
    (p : P.Chord → Fin 3 → ℝ) : ℂ :=
  ∏ c : P.Chord, massShellWeight m C ![α c.1, α (P.mate c.1)] (p c)

lemma measurable_wickChordWeight {κ : Type*} {n : ℕ} {m : ℝ}
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (P : ChordPairing n) (α : Fin n → κ) :
    Measurable (wickChordWeight m C P α) :=
  Finset.measurable_prod Finset.univ (fun c _ =>
    (measurable_massShellWeight hC ![α c.1, α (P.mate c.1)]).comp (measurable_pi_apply c))

lemma exists_norm_wickChordWeight_le {κ : Type*} {n : ℕ} {m : ℝ}
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (P : ChordPairing n) (α : Fin n → κ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : P.Chord → Fin 3 → ℝ, ‖wickChordWeight m C P α p‖ ≤ B := by
  let Bc : P.Chord → ℝ := fun c => Classical.choose (hC.2 ![α c.1, α (P.mate c.1)])
  have hBc : ∀ c : P.Chord,
      0 ≤ Bc c ∧ ∀ q : Fin 3 → ℝ, ‖massShellWeight m C ![α c.1, α (P.mate c.1)] q‖ ≤ Bc c :=
    fun c => Classical.choose_spec (hC.2 ![α c.1, α (P.mate c.1)])
  refine ⟨∏ c : P.Chord, Bc c, Finset.prod_nonneg (fun c _ => (hBc c).1), fun p => ?_⟩
  unfold wickChordWeight
  rw [norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun c _ => (hBc c).2 (p c))

lemma integrable_chordDecay {n : ℕ} (P : ChordPairing n) :
    Integrable (fun p : P.Chord → Fin 3 → ℝ => ∏ c : P.Chord, ((1 + ‖p c‖) ^ 4)⁻¹) volume :=
  Integrable.fintype_prod (f := fun _ : P.Chord => fun q : Fin 3 → ℝ => ((1 + ‖q‖) ^ 4)⁻¹)
    (fun _ => integrable_massShellDecay)

theorem integrable_wickChordWeight_mul_schwartz {κ : Type*} {n : ℕ} {m : ℝ}
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (P : ChordPairing n) (α : Fin n → κ)
    (g : SchwartzMap (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ) :
    Integrable (fun p : P.Chord → Fin 3 → ℝ =>
      wickChordWeight m C P α p * g (momentumToEuclidCLMN n (P.momentum m p))) volume := by
  rcases exists_norm_wickChordWeight_le hC P α with ⟨B, hB_nn, hB⟩
  let Kg : ℝ := (4 * Real.pi) ^ (4 * Fintype.card P.Chord) *
    ((Finset.Iic (4 * Fintype.card P.Chord, 0)).sup
      (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ) g)
  have h_meas_g : Measurable (fun p : P.Chord → Fin 3 → ℝ =>
      g (momentumToEuclidCLMN n (P.momentum m p))) :=
    (g.continuous.comp (momentumToEuclidCLMN n).continuous).measurable.comp
      (P.measurable_momentum m)
  refine Integrable.mono' ((integrable_chordDecay P).const_mul (B * Kg))
    ((measurable_wickChordWeight hC P α).mul h_meas_g).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => ?_))
  rw [norm_mul]
  calc ‖wickChordWeight m C P α p‖ * ‖g (momentumToEuclidCLMN n (P.momentum m p))‖
      ≤ B * (Kg * ∏ c : P.Chord, ((1 + ‖p c‖) ^ 4)⁻¹) :=
        mul_le_mul (hB p) (P.norm_schwartz_momentumToEuclid_chord_le m g p)
          (norm_nonneg _) hB_nn
    _ = (B * Kg) * ∏ c : P.Chord, ((1 + ‖p c‖) ^ 4)⁻¹ := by ring

noncomputable def wickChordEuclidCLM {κ : Type*} {n : ℕ} (m : ℝ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C)
    (P : ChordPairing n) (α : Fin n → κ) :
    SchwartzMap (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ →L[ℂ] ℂ :=
  SchwartzMap.mkCLMtoNormedSpace
    (fun g => ∫ p : P.Chord → Fin 3 → ℝ,
      wickChordWeight m C P α p * g (momentumToEuclidCLMN n (P.momentum m p)))
    (fun g₁ g₂ => by
      have h_add :
          (fun p : P.Chord → Fin 3 → ℝ =>
            wickChordWeight m C P α p *
              (g₁ + g₂) (momentumToEuclidCLMN n (P.momentum m p))) =
          fun p =>
            wickChordWeight m C P α p * g₁ (momentumToEuclidCLMN n (P.momentum m p)) +
            wickChordWeight m C P α p * g₂ (momentumToEuclidCLMN n (P.momentum m p)) := by
        ext p
        simp [mul_add]
      rw [h_add]
      exact integral_add (integrable_wickChordWeight_mul_schwartz hC P α g₁)
        (integrable_wickChordWeight_mul_schwartz hC P α g₂))
    (fun c g => by
      have h_smul :
          (fun p : P.Chord → Fin 3 → ℝ =>
            wickChordWeight m C P α p *
              (c • g) (momentumToEuclidCLMN n (P.momentum m p))) =
          fun p =>
            c * (wickChordWeight m C P α p * g (momentumToEuclidCLMN n (P.momentum m p))) := by
        ext p
        simp [smul_eq_mul, mul_left_comm]
      rw [h_smul, RingHom.id_apply, smul_eq_mul, integral_const_mul])
    (by
      let B : ℝ := Classical.choose (exists_norm_wickChordWeight_le hC P α)
      have hB_spec := Classical.choose_spec (exists_norm_wickChordWeight_le hC P α)
      have hB_nn : 0 ≤ B := hB_spec.1
      have hB : ∀ p : P.Chord → Fin 3 → ℝ, ‖wickChordWeight m C P α p‖ ≤ B := hB_spec.2
      let k := Fintype.card P.Chord
      let I_dec : ℝ := ∫ p : P.Chord → Fin 3 → ℝ, ∏ c : P.Chord, ((1 + ‖p c‖) ^ 4)⁻¹
      have hI_nn : 0 ≤ I_dec :=
        integral_nonneg (fun p => Finset.prod_nonneg (fun _ _ => by positivity))
      refine ⟨Finset.Iic (4 * k, 0), B * (4 * Real.pi) ^ (4 * k) * I_dec, by positivity,
        fun g => ?_⟩
      let S : ℝ := (Finset.Iic (4 * k, 0)).sup
        (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ) g
      calc ‖∫ p : P.Chord → Fin 3 → ℝ,
              wickChordWeight m C P α p * g (momentumToEuclidCLMN n (P.momentum m p))‖
          ≤ ∫ p : P.Chord → Fin 3 → ℝ,
              ‖wickChordWeight m C P α p * g (momentumToEuclidCLMN n (P.momentum m p))‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ p : P.Chord → Fin 3 → ℝ,
              (B * ((4 * Real.pi) ^ (4 * k) * S)) *
                ∏ c : P.Chord, ((1 + ‖p c‖) ^ 4)⁻¹ := by
            refine integral_mono_of_nonneg
              (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
              ((integrable_chordDecay P).const_mul (B * ((4 * Real.pi) ^ (4 * k) * S)))
              (Filter.Eventually.of_forall (fun p => ?_))
            dsimp only
            rw [norm_mul]
            calc ‖wickChordWeight m C P α p‖ *
                  ‖g (momentumToEuclidCLMN n (P.momentum m p))‖
                ≤ B * (((4 * Real.pi) ^ (4 * k) * S) *
                    ∏ c : P.Chord, ((1 + ‖p c‖) ^ 4)⁻¹) :=
                  mul_le_mul (hB p) (P.norm_schwartz_momentumToEuclid_chord_le m g p)
                    (norm_nonneg _) hB_nn
              _ = (B * ((4 * Real.pi) ^ (4 * k) * S)) *
                    ∏ c : P.Chord, ((1 + ‖p c‖) ^ 4)⁻¹ := by ring
        _ = (B * (4 * Real.pi) ^ (4 * k) * I_dec) * S := by
            rw [integral_const_mul]
            dsimp [I_dec]
            ring)

noncomputable def wickMassShellEuclidCLM {κ : Type*} {n : ℕ} (m : ℝ) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C) (α : Fin n → κ) :
    SchwartzMap (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ →L[ℂ] ℂ :=
  ∑ P : ChordPairing n, (η ^ P.cross) • wickChordEuclidCLM m C hC P α

noncomputable def wickMassShellW {κ : Type*} (m : ℝ) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C) :
    WightmanFamily κ :=
  fun n α =>
    PointwiseConvergenceCLM.precomp ℂ (minkowskiFourierSchwartzCLM n)
      (ContinuousLinearMap.toPointwiseConvergenceCLM _ _ _ _
        (wickMassShellEuclidCLM m η C hC α))

theorem integrable_wickChordWeight_mul_minkowskiFourier {κ : Type*} {n : ℕ} {m : ℝ}
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (P : ChordPairing n) (α : Fin n → κ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    Integrable (fun p : P.Chord → Fin 3 → ℝ =>
      wickChordWeight m C P α p * minkowskiFourier f (P.momentum m p)) volume := by
  have h_eq :
      (fun p : P.Chord → Fin 3 → ℝ =>
        wickChordWeight m C P α p * minkowskiFourier f (P.momentum m p)) =
      fun p =>
        wickChordWeight m C P α p *
          (minkowskiFourierSchwartzCLM n f) (momentumToEuclidCLMN n (P.momentum m p)) := by
    ext p
    rw [minkowskiFourier_eq_minkowskiFourierSchwartzCLM n f]
  rw [h_eq]
  exact integrable_wickChordWeight_mul_schwartz hC P α (minkowskiFourierSchwartzCLM n f)

theorem wickMassShellW_apply {κ : Type*} (m : ℝ) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C)
    (n : ℕ) (α : Fin n → κ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    wickMassShellW m η C hC n α f =
      ∑ P : ChordPairing n, η ^ P.cross *
        ∫ p : P.Chord → Fin 3 → ℝ,
          wickChordWeight m C P α p * minkowskiFourier f (P.momentum m p) := by
  change (wickMassShellEuclidCLM m η C hC α) (minkowskiFourierSchwartzCLM n f) = _
  simp only [wickMassShellEuclidCLM, FunLike.coe_sum,
    FunLike.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun P _ => congrArg (η ^ P.cross * ·) ?_)
  change ∫ p : P.Chord → Fin 3 → ℝ,
    wickChordWeight m C P α p *
      (minkowskiFourierSchwartzCLM n f) (momentumToEuclidCLMN n (P.momentum m p)) = _
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  dsimp only
  rw [← minkowskiFourier_eq_minkowskiFourierSchwartzCLM n f (P.momentum m p)]

noncomputable def wickMassShellH {κ : Type*} (m : ℝ) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (n : ℕ) (α : Fin n → κ)
    (z : Fin n → Fin 4 → ℂ) : ℂ :=
  ∑ P : ChordPairing n, η ^ P.cross *
    ∏ c : P.Chord,
      massShellTwoPointH m C 2 ![α c.1, α (P.mate c.1)] ![z c.1, z (P.mate c.1)]

theorem wickMassShellH_eq_sum_integral {κ : Type*} (m : ℝ) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (n : ℕ) (α : Fin n → κ)
    (z : Fin n → Fin 4 → ℂ) :
    wickMassShellH m η C n α z =
      ∑ P : ChordPairing n, η ^ P.cross *
        ∫ p : P.Chord → Fin 3 → ℝ,
          wickChordWeight m C P α p * vladimirov_kernel n z (P.momentum m p) := by
  unfold wickMassShellH
  refine Finset.sum_congr rfl (fun P _ => congrArg (η ^ P.cross * ·) ?_)
  have h_prod := (MeasureTheory.integral_fintype_prod_volume_eq_prod
    (E := fun _ : P.Chord => Fin 3 → ℝ)
    (f := fun (c : P.Chord) (q : Fin 3 → ℝ) =>
      massShellWeight m C ![α c.1, α (P.mate c.1)] q *
        vladimirov_kernel 2 ![z c.1, z (P.mate c.1)]
          (twoPointMomentum (massShellVec m q)))).symm
  simp only [massShellTwoPointH_two]
  rw [h_prod]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  dsimp only [wickChordWeight]
  rw [Finset.prod_mul_distrib, ← P.vladimirov_kernel_momentum m z p]

theorem analyticOn_wickMassShellH {κ : Type*} {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (n : ℕ) (α : Fin n → κ) :
    AnalyticOn ℂ (wickMassShellH m η C n α) (forward_tube_n n) := by
  rw [(forward_tube_n_isOpen n).analyticOn_iff_analyticOnNhd]
  intro z hz
  unfold wickMassShellH
  have h_prod_an : ∀ P : ChordPairing n,
      ∀ s : Finset P.Chord, AnalyticAt ℂ
        (fun w : Fin n → Fin 4 → ℂ =>
          ∏ c ∈ s, massShellTwoPointH m C 2 ![α c.1, α (P.mate c.1)] ![w c.1, w (P.mate c.1)])
        z := by
    intro P s
    induction s using Finset.induction_on with
    | empty => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ => (1 : ℂ)) z)
    | insert c s hc ih =>
        have h_eq :
            (fun w : Fin n → Fin 4 → ℂ =>
              ∏ c' ∈ insert c s,
                massShellTwoPointH m C 2 ![α c'.1, α (P.mate c'.1)]
                  ![w c'.1, w (P.mate c'.1)]) =
            fun w =>
              massShellTwoPointH m C 2 ![α c.1, α (P.mate c.1)] ![w c.1, w (P.mate c.1)] *
                ∏ c' ∈ s,
                  massShellTwoPointH m C 2 ![α c'.1, α (P.mate c'.1)]
                    ![w c'.1, w (P.mate c'.1)] := by
          ext w
          exact Finset.prod_insert hc
        rw [h_eq]
        have hz_pair : pairProjCLM c.1 (P.mate c.1) z ∈ forward_tube_n 2 := by
          rw [pairProjCLM_apply]
          exact pair_mem_forward_tube_two hz c.2
        have h_an2 := ((forward_tube_n_isOpen 2).analyticOn_iff_analyticOnNhd.mp
          (analyticOn_massShellTwoPointH hm hC 2 ![α c.1, α (P.mate c.1)]))
          (pairProjCLM c.1 (P.mate c.1) z) hz_pair
        exact (h_an2.comp_of_eq ((pairProjCLM c.1 (P.mate c.1)).analyticAt z) rfl).mul ih
  have h_sum_an : ∀ s : Finset (ChordPairing n),
      AnalyticAt ℂ
        (fun w : Fin n → Fin 4 → ℂ =>
          ∑ P ∈ s, η ^ P.cross *
            ∏ c : P.Chord,
              massShellTwoPointH m C 2 ![α c.1, α (P.mate c.1)] ![w c.1, w (P.mate c.1)])
        z := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ => (0 : ℂ)) z)
    | insert P s hP ih =>
        have h_eq :
            (fun w : Fin n → Fin 4 → ℂ =>
              ∑ Q ∈ insert P s, η ^ Q.cross *
                ∏ c : Q.Chord,
                  massShellTwoPointH m C 2 ![α c.1, α (Q.mate c.1)] ![w c.1, w (Q.mate c.1)]) =
            fun w =>
              η ^ P.cross *
                (∏ c : P.Chord,
                  massShellTwoPointH m C 2 ![α c.1, α (P.mate c.1)] ![w c.1, w (P.mate c.1)]) +
              ∑ Q ∈ s, η ^ Q.cross *
                ∏ c : Q.Chord,
                  massShellTwoPointH m C 2 ![α c.1, α (Q.mate c.1)] ![w c.1, w (Q.mate c.1)] := by
          ext w
          exact Finset.sum_insert hP
        rw [h_eq]
        exact (analyticAt_const.mul (h_prod_an P Finset.univ)).add ih
  exact h_sum_an Finset.univ

lemma integrable_prod_wickChordWeight_line_mul_f {κ : Type*} {n : ℕ} {m : ℝ} (hm : 0 < m)
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (P : ChordPairing n) (α : Fin n → κ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    {v : Fin 4 → ℝ} (hv : v ∈ forward_light_cone) {t : ℝ} (ht : 0 < t) :
    Integrable
      (Function.uncurry (fun (p : P.Chord → Fin 3 → ℝ) (x : Fin n → Fin 4 → ℝ) =>
        wickChordWeight m C P α p *
          (vladimirov_kernel n (tubeBoundaryLine n x v t) (P.momentum m p) * f x)))
      (volume.prod volume) := by
  let Bc : P.Chord → ℝ := fun c => Classical.choose (hC.2 ![α c.1, α (P.mate c.1)])
  have hBc : ∀ c : P.Chord,
      0 ≤ Bc c ∧ ∀ q : Fin 3 → ℝ, ‖massShellWeight m C ![α c.1, α (P.mate c.1)] q‖ ≤ Bc c :=
    fun c => Classical.choose_spec (hC.2 ![α c.1, α (P.mate c.1)])
  let c₀ : ℝ := t * coneGap v
  have hc₀ : 0 < c₀ := mul_pos ht (coneGap_pos v hv)
  have h_dom_p : Integrable
      (fun p : P.Chord → Fin 3 → ℝ =>
        ∏ c : P.Chord, (Bc c * Real.exp (-(c₀ * massShellEnergy m (p c))))) volume :=
    Integrable.fintype_prod
      (f := fun c : P.Chord => fun q : Fin 3 → ℝ =>
        Bc c * Real.exp (-(c₀ * massShellEnergy m q)))
      (fun c => (integrable_exp_neg_massShellEnergy hm hc₀).const_mul (Bc c))
  have h_dom : Integrable
      (fun px : (P.Chord → Fin 3 → ℝ) × (Fin n → Fin 4 → ℝ) =>
        (∏ c : P.Chord, (Bc c * Real.exp (-(c₀ * massShellEnergy m (px.1 c))))) * ‖f px.2‖)
      (volume.prod volume) :=
    h_dom_p.mul_prod f.integrable.norm
  have h_meas_ker : Measurable
      (fun px : (P.Chord → Fin 3 → ℝ) × (Fin n → Fin 4 → ℝ) =>
        vladimirov_kernel n (tubeBoundaryLine n px.2 v t) (P.momentum m px.1)) := by
    have h_phase : Measurable
        (fun px : (P.Chord → Fin 3 → ℝ) × (Fin n → Fin 4 → ℝ) =>
          -Complex.I * ∑ k : Fin n,
            minkowskiInnerC
              (fun μ => (P.momentum m px.1 k μ : ℂ))
              (tubeBoundaryLine n px.2 v t k)) := by
      refine measurable_const.mul (Finset.measurable_sum Finset.univ (fun k _ => ?_))
      have hk1 : Measurable
          (fun px : (P.Chord → Fin 3 → ℝ) × (Fin n → Fin 4 → ℝ) => P.momentum m px.1 k) :=
        (measurable_pi_apply k).comp ((P.measurable_momentum m).comp measurable_fst)
      have hk2 : Measurable
          (fun px : (P.Chord → Fin 3 → ℝ) × (Fin n → Fin 4 → ℝ) => px.2 k) :=
        (measurable_pi_apply k).comp measurable_snd
      have hm1 : ∀ μ : Fin 4, Measurable
          (fun px : (P.Chord → Fin 3 → ℝ) × (Fin n → Fin 4 → ℝ) =>
            (P.momentum m px.1 k μ : ℂ)) :=
        fun μ => Complex.continuous_ofReal.measurable.comp ((measurable_pi_apply μ).comp hk1)
      have hm2 : ∀ μ : Fin 4, Measurable
          (fun px : (P.Chord → Fin 3 → ℝ) × (Fin n → Fin 4 → ℝ) =>
            tubeBoundaryLine n px.2 v t k μ) :=
        fun μ => (Complex.continuous_ofReal.measurable.comp
          ((measurable_pi_apply μ).comp hk2)).add measurable_const
      exact (((hm1 0).mul (hm2 0)).sub ((hm1 1).mul (hm2 1))).sub
        ((hm1 2).mul (hm2 2)) |>.sub ((hm1 3).mul (hm2 3))
    exact Complex.continuous_exp.measurable.comp h_phase
  have h_meas : AEStronglyMeasurable
      (fun px : (P.Chord → Fin 3 → ℝ) × (Fin n → Fin 4 → ℝ) =>
        wickChordWeight m C P α px.1 *
          (vladimirov_kernel n (tubeBoundaryLine n px.2 v t) (P.momentum m px.1) * f px.2))
      (volume.prod volume) :=
    (((measurable_wickChordWeight hC P α).comp measurable_fst).aestronglyMeasurable).mul
      (h_meas_ker.aestronglyMeasurable.mul f.integrable.aestronglyMeasurable.comp_snd)
  refine Integrable.mono' h_dom h_meas (Filter.Eventually.of_forall (fun px => ?_))
  dsimp only [Function.uncurry]
  rw [norm_mul, norm_mul, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg (f px.2))
  rw [P.vladimirov_kernel_momentum m (tubeBoundaryLine n px.2 v t) px.1]
  unfold wickChordWeight
  rw [norm_prod, norm_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun c _ => ?_)
  let zc : Fin 2 → Fin 4 → ℂ :=
    ![tubeBoundaryLine n px.2 v t c.1, tubeBoundaryLine n px.2 v t (P.mate c.1)]
  have hzc : zc ∈ forward_tube_n 2 :=
    pair_mem_forward_tube_two (line_mem_forward_tube n px.2 v hv t ht) c.2
  have hd_ge_one : (1 : ℝ) ≤ ((P.mate c.1 : ℕ) : ℝ) - ((c.1 : ℕ) : ℝ) := by
    have hlt : (c.1 : ℕ) + 1 ≤ (P.mate c.1 : ℕ) := c.2
    have hlt_r : ((c.1 : ℕ) : ℝ) + 1 ≤ ((P.mate c.1 : ℕ) : ℝ) := by exact_mod_cast hlt
    linarith
  let s_c : ℝ := t * (((P.mate c.1 : ℕ) : ℝ) - ((c.1 : ℕ) : ℝ))
  have hs_pos : 0 < s_c := mul_pos ht (by linarith)
  have h_diff_zc : diff_im 2 zc 0 (by decide) = s_c • v := by
    ext μ
    change -((zc 0 - zc 1) μ).im = s_c * v μ
    have hz0 : zc 0 μ = tubeBoundaryLine n px.2 v t c.1 μ := rfl
    have hz1 : zc 1 μ = tubeBoundaryLine n px.2 v t (P.mate c.1) μ := rfl
    rw [Pi.sub_apply, hz0, hz1]
    dsimp only [tubeBoundaryLine, s_c]
    rw [sub_im, add_im, add_im, ofReal_im, ofReal_im, mul_im, mul_im,
      ofReal_re, ofReal_re, I_re, I_im]
    ring
  have h_gap_zc : coneGap (diff_im 2 zc 0 (by decide)) = s_c * coneGap v := by
    rw [h_diff_zc]
    dsimp [coneGap]
    have h_sq : ((s_c * v 1) ^ 2 + (s_c * v 2) ^ 2 + (s_c * v 3) ^ 2) =
        s_c ^ 2 * ((v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2) := by ring
    rw [h_sq, Real.sqrt_mul (sq_nonneg s_c), Real.sqrt_sq hs_pos.le]
    ring
  have h_c0_le : c₀ ≤ coneGap (diff_im 2 zc 0 (by decide)) := by
    rw [h_gap_zc]
    dsimp [c₀, s_c]
    have hcg : 0 ≤ coneGap v := (coneGap_pos v hv).le
    have ht_le : t ≤ t * (((P.mate c.1 : ℕ) : ℝ) - ((c.1 : ℕ) : ℝ)) :=
      le_mul_of_one_le_right ht.le hd_ge_one
    exact mul_le_mul_of_nonneg_right ht_le hcg
  have h_ker_le :
      ‖vladimirov_kernel 2 zc (twoPointMomentum (massShellVec m (px.1 c)))‖ ≤
        Real.exp (-(c₀ * massShellEnergy m (px.1 c))) := by
    refine (norm_vladimirov_kernel_twoPoint_le_exp hm hzc (px.1 c)).trans ?_
    apply Real.exp_le_exp.mpr
    have hω_nn : 0 ≤ massShellEnergy m (px.1 c) := (massShellEnergy_pos hm (px.1 c)).le
    nlinarith [mul_le_mul_of_nonneg_right h_c0_le hω_nn]
  exact mul_le_mul ((hBc c).2 (px.1 c)) h_ker_le (norm_nonneg _) (hBc c).1

theorem tendsto_wickMassShellH_boundary {κ : Type*} {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (n : ℕ) (α : Fin n → κ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    {v : Fin 4 → ℝ} (hv : v ∈ forward_light_cone) :
    Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        wickMassShellH m η C n α (tubeBoundaryLine n x v t) * f x)
      (𝓝[>] 0)
      (𝓝 (wickMassShellW m η C hC n α f)) := by
  rw [wickMassShellW_apply]
  have h_sum_eq :
      (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        wickMassShellH m η C n α (tubeBoundaryLine n x v t) * f x) =ᶠ[𝓝[>] 0]
      fun t : ℝ => ∑ P : ChordPairing n, η ^ P.cross *
        ∫ p : P.Chord → Fin 3 → ℝ,
          wickChordWeight m C P α p *
            (Complex.exp (t * ∑ k : Fin n, ((k : ℕ) : ℝ) *
              minkowskiInner (P.momentum m p k) v : ℂ) *
              minkowskiFourier f (P.momentum m p)) := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have h_int_x : ∀ P : ChordPairing n,
        Integrable (fun x : Fin n → Fin 4 → ℝ =>
          η ^ P.cross *
            ((∫ p : P.Chord → Fin 3 → ℝ,
              wickChordWeight m C P α p *
                vladimirov_kernel n (tubeBoundaryLine n x v t) (P.momentum m p)) * f x))
          volume := by
      intro P
      have h_fub :=
        (integrable_prod_wickChordWeight_line_mul_f hm hC P α f hv ht).integral_prod_right
      have h_eq_fn : ∀ x : Fin n → Fin 4 → ℝ,
          (∫ p : P.Chord → Fin 3 → ℝ,
            wickChordWeight m C P α p *
              vladimirov_kernel n (tubeBoundaryLine n x v t) (P.momentum m p)) * f x =
          ∫ p : P.Chord → Fin 3 → ℝ,
            wickChordWeight m C P α p *
              (vladimirov_kernel n (tubeBoundaryLine n x v t) (P.momentum m p) * f x) := by
        intro x
        rw [← integral_mul_const]
        exact integral_congr_ae (Filter.Eventually.of_forall (fun _ => mul_assoc _ _ _))
      simp_rw [h_eq_fn]
      exact h_fub.const_mul (η ^ P.cross)
    have h_expand :
        (fun x : Fin n → Fin 4 → ℝ =>
          wickMassShellH m η C n α (tubeBoundaryLine n x v t) * f x) =
        fun x => ∑ P : ChordPairing n, η ^ P.cross *
          ((∫ p : P.Chord → Fin 3 → ℝ,
            wickChordWeight m C P α p *
              vladimirov_kernel n (tubeBoundaryLine n x v t) (P.momentum m p)) * f x) := by
      ext x
      rw [wickMassShellH_eq_sum_integral, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ => mul_assoc _ _ _)
    rw [h_expand, integral_finsetSum Finset.univ (fun P _ => h_int_x P)]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [integral_const_mul]
    congr 1
    have h_lhs :
        (fun x : Fin n → Fin 4 → ℝ =>
          (∫ p : P.Chord → Fin 3 → ℝ,
            wickChordWeight m C P α p *
              vladimirov_kernel n (tubeBoundaryLine n x v t) (P.momentum m p)) * f x) =
        fun x => ∫ p : P.Chord → Fin 3 → ℝ,
          wickChordWeight m C P α p *
            (vladimirov_kernel n (tubeBoundaryLine n x v t) (P.momentum m p) * f x) := by
      ext x
      rw [← integral_mul_const]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun _ => mul_assoc _ _ _))
    rw [h_lhs,
        (MeasureTheory.integral_integral_swap
          (integrable_prod_wickChordWeight_line_mul_f hm hC P α f hv ht)).symm]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    dsimp only
    rw [integral_const_mul, integral_vladimirov_kernel_line_mul_f n f (P.momentum m p) v t]
  rw [tendsto_congr' h_sum_eq]
  refine tendsto_finsetSum Finset.univ (fun P _ => Tendsto.const_mul (η ^ P.cross) ?_)
  rcases exists_norm_wickChordWeight_le hC P α with ⟨B, hB_nn, hB⟩
  let g_hat := minkowskiFourierSchwartzCLM n f
  let Kf : ℝ := (4 * Real.pi) ^ (4 * Fintype.card P.Chord) *
    ((Finset.Iic (4 * Fintype.card P.Chord, 0)).sup
      (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ) g_hat)
  let G : ℝ → (P.Chord → Fin 3 → ℝ) → ℂ := fun t p =>
    wickChordWeight m C P α p *
      (Complex.exp (t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (P.momentum m p k) v : ℂ) *
        minkowskiFourier f (P.momentum m p))
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun p => (B * Kf) * ∏ c : P.Chord, ((1 + ‖p c‖) ^ 4)⁻¹) ?_ ?_
    ((integrable_chordDecay P).const_mul (B * Kf)) ?_
  · refine Filter.Eventually.of_forall (fun t => ?_)
    have h_cont_q : Continuous (fun q : Fin n → Fin 4 → ℝ =>
        Complex.exp (t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (q k) v : ℂ) *
          minkowskiFourier f q) := by
      have h_lin : Continuous (fun q : Fin n → Fin 4 → ℝ =>
          (t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (q k) v : ℂ)) := by
        have h_real : Continuous (fun q : Fin n → Fin 4 → ℝ =>
            t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (q k) v) := by
          refine continuous_const.mul (continuous_finsetSum Finset.univ (fun k _ => ?_))
          refine continuous_const.mul ?_
          simp only [minkowskiInner_explicit]
          have hc : ∀ μ : Fin 4, Continuous (fun q : Fin n → Fin 4 → ℝ => q k μ) :=
            fun μ => (continuous_apply μ).comp (continuous_apply k)
          exact (((hc 0).mul continuous_const).sub ((hc 1).mul continuous_const)).sub
            ((hc 2).mul continuous_const) |>.sub ((hc 3).mul continuous_const)
        have h_eq_c : (fun q : Fin n → Fin 4 → ℝ =>
            (t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (q k) v : ℂ)) =
            fun q => ((t * ∑ k : Fin n, ((k : ℕ) : ℝ) *
              minkowskiInner (q k) v : ℝ) : ℂ) := by
          ext q
          push_cast
          rfl
        rw [h_eq_c]
        exact Complex.continuous_ofReal.comp h_real
      exact (Complex.continuous_exp.comp h_lin).mul (continuous_minkowskiFourier n f)
    exact ((measurable_wickChordWeight hC P α).mul
      (h_cont_q.measurable.comp (P.measurable_momentum m))).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    refine Filter.Eventually.of_forall (fun p => ?_)
    rw [norm_mul, norm_mul]
    have hp_cone := P.momentum_mem_forwardConeSpectralRegion hm p
    have h_exp_le :
        ‖Complex.exp (t * ∑ k : Fin n, ((k : ℕ) : ℝ) *
          minkowskiInner (P.momentum m p k) v : ℂ)‖ ≤ 1 := by
      have h_cast :
          (t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (P.momentum m p k) v : ℂ) =
          ((t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (P.momentum m p k) v : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [h_cast, Complex.norm_exp_ofReal]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ht.le
        (sum_k_minkowskiInner_le_zero_of_forwardConeSpectralRegion n hp_cone hv))
    have h_four_le :
        ‖minkowskiFourier f (P.momentum m p)‖ ≤
          Kf * ∏ c : P.Chord, ((1 + ‖p c‖) ^ 4)⁻¹ := by
      rw [minkowskiFourier_eq_minkowskiFourierSchwartzCLM n f]
      exact P.norm_schwartz_momentumToEuclid_chord_le m g_hat p
    calc ‖wickChordWeight m C P α p‖ *
          (‖Complex.exp (t * ∑ k : Fin n, ((k : ℕ) : ℝ) *
            minkowskiInner (P.momentum m p k) v : ℂ)‖ *
            ‖minkowskiFourier f (P.momentum m p)‖)
        ≤ B * (Kf * ∏ c : P.Chord, ((1 + ‖p c‖) ^ 4)⁻¹) :=
          mul_le_mul (hB p)
            ((mul_le_of_le_one_left (norm_nonneg _) h_exp_le).trans h_four_le)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hB_nn
      _ = (B * Kf) * ∏ c : P.Chord, ((1 + ‖p c‖) ^ 4)⁻¹ := by ring
  · refine Filter.Eventually.of_forall (fun p => ?_)
    have h_cont_t : Continuous (fun t : ℝ => G t p) :=
      continuous_const.mul
        ((Complex.continuous_exp.comp
          (Complex.continuous_ofReal.mul continuous_const)).mul continuous_const)
    have h0 : G 0 p = wickChordWeight m C P α p * minkowskiFourier f (P.momentum m p) := by
      dsimp [G]
      simp
    rw [← h0]
    exact (h_cont_t.tendsto 0).mono_left nhdsWithin_le_nhds

noncomputable def wickMassShellTubeExtension {κ : Type*} (m : ℝ) (hm : 0 < m) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C) :
    TubeExtension (wickMassShellW m η C hC) where
  H := wickMassShellH m η C
  analytic n α := analyticOn_wickMassShellH hm η hC n α
  boundary n α f _v hv := tendsto_wickMassShellH_boundary hm η hC n α f hv

@[simp]
theorem wickMassShellTubeExtension_H {κ : Type*} (m : ℝ) (hm : 0 < m) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C) :
    (wickMassShellTubeExtension m hm η C hC).H = wickMassShellH m η C := rfl

noncomputable def wickMassShellS {κ : Type*} (m : ℝ) (hm : 0 < m) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C) :
    SchwingerFamily κ :=
  schwingerFromTube (wickMassShellTubeExtension m hm η C hC)

theorem wickMassShellS_apply {κ : Type*} (m : ℝ) (hm : 0 < m) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C)
    (n : ℕ) (α : Fin n → κ) (x : Fin n → Fin 4 → ℝ) :
    wickMassShellS m hm η C hC n α x =
      ∑ P : ChordPairing n, η ^ P.cross *
        ∏ c : P.Chord,
          massShellTwoPointS m hm C hC 2 ![α c.1, α (P.mate c.1)] ![x c.1, x (P.mate c.1)] := by
  change wickMassShellH m η C n α (wickEmbedN n x) = _
  unfold wickMassShellH
  refine Finset.sum_congr rfl (fun P _ => congrArg (η ^ P.cross * ·) ?_)
  refine Finset.prod_congr rfl (fun c _ => ?_)
  have h_emb : ![wickEmbedN n x c.1, wickEmbedN n x (P.mate c.1)] =
      wickEmbedN 2 ![x c.1, x (P.mate c.1)] := by
    ext s μ
    fin_cases s <;> rfl
  rw [h_emb]
  rfl

@[simp]
theorem wickMassShellH_zero {κ : Type*} (m : ℝ) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (α : Fin 0 → κ) (z : Fin 0 → Fin 4 → ℂ) :
    wickMassShellH m η C 0 α z = 1 := by
  unfold wickMassShellH
  rw [Fintype.sum_unique]
  haveI : IsEmpty (default : ChordPairing 0).Chord := ⟨fun c => Fin.elim0 c.1⟩
  have hcross : (default : ChordPairing 0).cross = 0 := rfl
  simp [hcross]

@[simp]
theorem wickMassShellS_zero {κ : Type*} (m : ℝ) (hm : 0 < m) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C)
    (α : Fin 0 → κ) (x : Fin 0 → Fin 4 → ℝ) :
    wickMassShellS m hm η C hC 0 α x = 1 :=
  wickMassShellH_zero m η C α (wickEmbedN 0 x)

@[simp]
theorem wickMassShellS_vacuumNormalized {κ : Type*} (m : ℝ) (hm : 0 < m) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C) :
    OSVacuumNormalized (wickMassShellS m hm η C hC) :=
  wickMassShellS_zero m hm η C hC Fin.elim0 0

@[simp]
theorem wickMassShellW_zero_apply {κ : Type*} (m : ℝ) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C)
    (α : Fin 0 → κ) (f : SchwartzMap (Fin 0 → Fin 4 → ℝ) ℂ) :
    wickMassShellW m η C hC 0 α f = f 0 := by
  rw [wickMassShellW_apply, Fintype.sum_unique]
  haveI : IsEmpty (default : ChordPairing 0).Chord := ⟨fun c => Fin.elim0 c.1⟩
  haveI : Unique ((default : ChordPairing 0).Chord → Fin 3 → ℝ) := Pi.uniqueOfIsEmpty _
  have hcross : (default : ChordPairing 0).cross = 0 := rfl
  have hm0 : (default : ChordPairing 0).momentum m default = 0 := by
    ext i
    exact Fin.elim0 i
  have hw0 : wickChordWeight m C (default : ChordPairing 0) α default = 1 := by
    simp [wickChordWeight]
  rw [hcross, pow_zero, one_mul]
  have h_vol : (volume : Measure ((default : ChordPairing 0).Chord → Fin 3 → ℝ)) =
      Measure.dirac default := by
    change Measure.pi (fun _ => volume) = Measure.dirac default
    exact Measure.pi_of_empty _ default
  rw [h_vol, integral_dirac, hw0, one_mul, hm0, minkowskiFourier_eval_zero_n, integral_fin0]

theorem wickMassShellH_eq_zero_of_odd {κ : Type*} (m : ℝ) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) {n : ℕ} (hn : Odd n)
    (α : Fin n → κ) (z : Fin n → Fin 4 → ℂ) :
    wickMassShellH m η C n α z = 0 := by
  haveI := ChordPairing.isEmpty_of_odd hn
  simp [wickMassShellH]

theorem wickMassShellS_eq_zero_of_odd {κ : Type*} (m : ℝ) (hm : 0 < m) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C)
    {n : ℕ} (hn : Odd n) (α : Fin n → κ) (x : Fin n → Fin 4 → ℝ) :
    wickMassShellS m hm η C hC n α x = 0 :=
  wickMassShellH_eq_zero_of_odd m η C hn α (wickEmbedN n x)

theorem wickMassShellW_eq_zero_of_odd {κ : Type*} (m : ℝ) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C)
    {n : ℕ} (hn : Odd n) (α : Fin n → κ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    wickMassShellW m η C hC n α f = 0 := by
  rw [wickMassShellW_apply]
  haveI := ChordPairing.isEmpty_of_odd hn
  simp

@[simp]
theorem wickMassShellH_two {κ : Type*} (m : ℝ) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ)
    (α : Fin 2 → κ) (z : Fin 2 → Fin 4 → ℂ) :
    wickMassShellH m η C 2 α z = massShellTwoPointH m C 2 α z := by
  unfold wickMassShellH
  rw [Fintype.sum_unique]
  change η ^ ChordPairing.twoPairing.cross *
    (∏ c ∈ (Finset.univ : Finset ChordPairing.twoPairing.Chord),
      massShellTwoPointH m C 2
        ![α c.1, α (ChordPairing.twoPairing.mate c.1)]
        ![z c.1, z (ChordPairing.twoPairing.mate c.1)]) = _
  rw [ChordPairing.cross_two, pow_zero, one_mul, ChordPairing.unique_twoPairing_chord,
      Finset.prod_singleton]
  change massShellTwoPointH m C 2 ![α 0, α 1] ![z 0, z 1] = _
  rw [(finTwo_eq_vecCons α).symm, (finTwo_eq_vecCons z).symm]

theorem wickMassShellW_two {κ : Type*} {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (α : Fin 2 → κ) :
    wickMassShellW m η C hC 2 α = massShellTwoPointW m C hC 2 α := by
  ext f
  have hv : unit_time_vector ∈ forward_light_cone := unit_time_vector_mem_forward_light_cone
  have hb1 := tendsto_wickMassShellH_boundary hm η hC 2 α f hv
  have hb2 := tendsto_massShellTwoPointH_boundary hm hC 2 α f hv
  have h_eq :
      (fun t : ℝ => ∫ x : Fin 2 → Fin 4 → ℝ,
        wickMassShellH m η C 2 α (tubeBoundaryLine 2 x unit_time_vector t) * f x) =
      fun t : ℝ => ∫ x : Fin 2 → Fin 4 → ℝ,
        massShellTwoPointH m C 2 α (tubeBoundaryLine 2 x unit_time_vector t) * f x := by
    ext t
    simp only [wickMassShellH_two]
  rw [h_eq] at hb1
  haveI : Filter.NeBot (𝓝[>] (0 : ℝ)) := nhdsWithin_Ioi_neBot le_rfl
  exact tendsto_nhds_unique hb1 hb2

theorem wickMassShell_forwardConeSpectrumCondition {κ : Type*} {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C) :
    ForwardConeSpectrumCondition (wickMassShellW m η C hC) := by
  intro n α f ⟨U, _hU_open, hU_sub, hU_zero⟩
  rw [wickMassShellW_apply]
  refine Finset.sum_eq_zero (fun P _ => ?_)
  have h_zero :
      (fun p : P.Chord → Fin 3 → ℝ =>
        wickChordWeight m C P α p * minkowskiFourier f (P.momentum m p)) =
      fun _ => 0 := by
    ext p
    rw [hU_zero (P.momentum m p) (hU_sub (P.momentum_mem_forwardConeSpectralRegion hm p)),
        mul_zero]
  rw [h_zero, integral_zero, mul_zero]

theorem wickMassShell_nondeg_and_not_zeroMomentum {κ : Type*} {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (α : Fin 2 → κ) {r : (Fin 3 → ℝ) → ℝ}
    (hr_cont : Continuous r) (hr_pos : ∀ p : Fin 3 → ℝ, 0 < r p)
    (hr_eq : ∀ p : Fin 3 → ℝ, C α (massShellVec m p) = (r p : ℂ)) :
    wickMassShellW m η C hC 2 α ≠ 0 ∧
      ¬ ZeroMomentumSpectrumCondition (wickMassShellW m η C hC) := by
  rcases massShellTwoPoint_nondeg_and_not_zeroMomentum hm hC α hr_cont hr_pos hr_eq with
    ⟨hne, hnot⟩
  refine ⟨by rwa [wickMassShellW_two hm η hC α], fun hspec => hnot ?_⟩
  intro n β f hf0
  match n with
  | 0 =>
      rw [minkowskiFourier_eval_zero_n, integral_fin0] at hf0
      rw [massShellTwoPointW_zero_apply, hf0]
  | 1 => rfl
  | _ + 3 => rfl
  | 2 =>
      rw [← wickMassShellW_two hm η hC β]
      exact hspec 2 β f hf0

theorem wickMassShellTubeTranslationInvariant {κ : Type*} {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C) :
    TubeTranslationInvariant (wickMassShellTubeExtension m hm η C hC) := by
  intro n α z a hz
  change wickMassShellH m η C n α (fun i => z i + a) = wickMassShellH m η C n α z
  unfold wickMassShellH
  refine Finset.sum_congr rfl (fun P _ => congrArg (η ^ P.cross * ·) ?_)
  refine Finset.prod_congr rfl (fun c _ => ?_)
  have h_pair : ![z c.1 + a, z (P.mate c.1) + a] =
      fun k : Fin 2 => ![z c.1, z (P.mate c.1)] k + a := by
    ext k μ
    fin_cases k <;> rfl
  rw [h_pair]
  exact massShellTwoPointTubeTranslationInvariant hm hC 2
    ![α c.1, α (P.mate c.1)] ![z c.1, z (P.mate c.1)] a
    (pair_mem_forward_tube_two hz c.2)

theorem wickMassShellOSTranslationInvariant {κ : Type*} {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C) :
    OSTranslationInvariant (wickMassShellS m hm η C hC) :=
  schwingerFromTube_translation_invariant
    (wickMassShellTubeExtension m hm η C hC)
    (wickMassShellTubeTranslationInvariant hm η hC)

theorem wickMassShellTubeCovariant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R.rep A (α i) (β i)) * C β q) :
    TubeCovariant R (wickMassShellTubeExtension m hm η C hC) := by
  intro n A z hz hAz α
  change wickMassShellH m η C n α (spinorPhi (A, sl2c_conj A) • z) =
    ∑ β : Fin n → ι, (∏ i : Fin n, R.rep A (α i) (β i)) * wickMassShellH m η C n β z
  unfold wickMassShellH
  have h_rhs_swap :
      (∑ β : Fin n → ι, (∏ i : Fin n, R.rep A (α i) (β i)) *
        ∑ P : ChordPairing n, η ^ P.cross *
          ∏ c : P.Chord,
            massShellTwoPointH m C 2 ![β c.1, β (P.mate c.1)] ![z c.1, z (P.mate c.1)]) =
      ∑ P : ChordPairing n, η ^ P.cross *
        ∑ β : Fin n → ι, (∏ i : Fin n, R.rep A (α i) (β i)) *
          ∏ c : P.Chord,
            massShellTwoPointH m C 2 ![β c.1, β (P.mate c.1)] ![z c.1, z (P.mate c.1)] := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    exact Finset.sum_congr rfl (fun β _ => by ring)
  rw [h_rhs_swap]
  refine Finset.sum_congr rfl (fun P _ => congrArg (η ^ P.cross * ·) ?_)
  rw [P.sum_prod_chord_factor (fun i b => R.rep A (α i) b)
    (fun c γ => massShellTwoPointH m C 2 γ ![z c.1, z (P.mate c.1)])]
  refine Finset.prod_congr rfl (fun c _ => ?_)
  have h_smul_pair :
      ![(spinorPhi (A, sl2c_conj A) • z) c.1,
        (spinorPhi (A, sl2c_conj A) • z) (P.mate c.1)] =
      spinorPhi (A, sl2c_conj A) • ![z c.1, z (P.mate c.1)] := by
    ext k μ
    fin_cases k <;> rfl
  have hz_pair := pair_mem_forward_tube_two hz c.2
  have hAz_pair : spinorPhi (A, sl2c_conj A) • ![z c.1, z (P.mate c.1)] ∈ forward_tube_n 2 := by
    rw [← h_smul_pair]
    exact pair_mem_forward_tube_two hAz c.2
  have h2 := massShellTwoPointTubeCovariant R hm hC hC_cov 2 A
    ![z c.1, z (P.mate c.1)] hz_pair hAz_pair ![α c.1, α (P.mate c.1)]
  change massShellTwoPointH m C 2 ![α c.1, α (P.mate c.1)]
      (spinorPhi (A, sl2c_conj A) • ![z c.1, z (P.mate c.1)]) =
    ∑ γ : Fin 2 → ι, (∏ i : Fin 2, R.rep A (![α c.1, α (P.mate c.1)] i) (γ i)) *
      massShellTwoPointH m C 2 γ ![z c.1, z (P.mate c.1)] at h2
  rw [h_smul_pair, h2]
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  rw [Fin.prod_univ_two]
  rfl

theorem wickMassShellPoincareCovariant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R.rep A (α i) (β i)) * C β q) :
    PoincareCovariant R (wickMassShellW m η C hC) :=
  poincareCovariant_of_tubeCovariant_general R (wickMassShellW m η C hC)
    (wickMassShellTubeExtension m hm η C hC)
    (wickMassShellTubeCovariant R hm η hC hC_cov)
    (wickMassShellTubeTranslationInvariant hm η hC)

theorem wickMassShellEuclidRotCovariant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R.rep A (α i) (β i)) * C β q) :
    EuclidRotCovariant R (wickMassShellS m hm η C hC) :=
  schwingerFromTube_euclidCovariant R (wickMassShellW m η C hC)
    (wickMassShellTubeExtension m hm η C hC)
    (wickMassShellTubeCovariant R hm η hC hC_cov)

theorem wickMassShellTubeWickHermiticity {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {m : ℝ} (hm : 0 < m) {η : ℂ} (hη : η = 1 ∨ η = -1)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q) :
    TubeWickHermiticity S (wickMassShellTubeExtension m hm η C hC) := by
  intro n α z hz hz_rev
  let z_rev : Fin n → Fin 4 → ℂ := fun i μ => star (z (Fin.rev i) μ)
  change star (wickMassShellH m η C n α z) =
    ∑ β : Fin n → ι, (∏ i : Fin n, S.C (α i) (β i)) * wickMassShellH m η C n (β ∘ Fin.rev) z_rev
  unfold wickMassShellH
  rw [star_sum]
  have h_rhs_swap :
      (∑ β : Fin n → ι, (∏ i : Fin n, S.C (α i) (β i)) *
        ∑ Q : ChordPairing n, η ^ Q.cross *
          ∏ c' : Q.Chord,
            massShellTwoPointH m C 2
              ![(β ∘ Fin.rev) c'.1, (β ∘ Fin.rev) (Q.mate c'.1)]
              ![z_rev c'.1, z_rev (Q.mate c'.1)]) =
      ∑ P : ChordPairing n, η ^ P.cross *
        ∑ β : Fin n → ι, (∏ i : Fin n, S.C (α i) (β i)) *
          ∏ c : P.Chord,
            massShellTwoPointH m C 2 (![β c.1, β (P.mate c.1)] ∘ Fin.rev)
              ![z_rev (Fin.rev (P.mate c.1)), z_rev (Fin.rev c.1)] := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, ← (ChordPairing.revEquiv n).sum_comp]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    have hrevP : ChordPairing.revEquiv n P = P.rev := rfl
    rw [hrevP, P.cross_rev]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [← P.revChordEquiv.prod_comp]
    have h_prod_eq :
        (∏ c : P.Chord,
          massShellTwoPointH m C 2
            ![(β ∘ Fin.rev) (P.revChordEquiv c).1,
              (β ∘ Fin.rev) (P.rev.mate (P.revChordEquiv c).1)]
            ![z_rev (P.revChordEquiv c).1, z_rev (P.rev.mate (P.revChordEquiv c).1)]) =
        ∏ c : P.Chord,
          massShellTwoPointH m C 2 (![β c.1, β (P.mate c.1)] ∘ Fin.rev)
            ![z_rev (Fin.rev (P.mate c.1)), z_rev (Fin.rev c.1)] := by
      refine Finset.prod_congr rfl (fun c _ => ?_)
      have hm_eq : P.rev.mate (P.revChordEquiv c).1 = Fin.rev c.1 := by
        change Fin.rev (P.mate (Fin.rev (Fin.rev (P.mate c.1)))) = Fin.rev c.1
        rw [Fin.rev_rev, P.mate_mate]
      have h1 : (P.revChordEquiv c).1 = Fin.rev (P.mate c.1) := rfl
      have hβ : ![(β ∘ Fin.rev) (Fin.rev (P.mate c.1)), (β ∘ Fin.rev) (Fin.rev c.1)] =
          ![β c.1, β (P.mate c.1)] ∘ Fin.rev := by
        ext k
        fin_cases k <;> simp [Fin.rev_rev]
      rw [hm_eq, h1, hβ]
    rw [h_prod_eq]
    ring
  rw [h_rhs_swap]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [star_mul', star_eta_pow hη]
  congr 1
  rw [Complex.star_def, map_prod]
  simp_rw [← Complex.star_def]
  rw [P.sum_prod_chord_factor (fun i b => S.C (α i) b)
    (fun c γ => massShellTwoPointH m C 2 (γ ∘ Fin.rev)
      ![z_rev (Fin.rev (P.mate c.1)), z_rev (Fin.rev c.1)])]
  refine Finset.prod_congr rfl (fun c _ => ?_)
  have hz_pair := pair_mem_forward_tube_two hz c.2
  have hz_rev_pair_eq :
      (fun k μ => star (![z c.1, z (P.mate c.1)] (Fin.rev k) μ)) =
      ![z_rev (Fin.rev (P.mate c.1)), z_rev (Fin.rev c.1)] := by
    ext k μ
    fin_cases k <;> simp [z_rev, Fin.rev_rev]
  have hz_rev_pair : (fun k μ => star (![z c.1, z (P.mate c.1)] (Fin.rev k) μ)) ∈
      forward_tube_n 2 := by
    rw [hz_rev_pair_eq]
    exact pair_mem_forward_tube_two hz_rev (Fin.rev_lt_rev.mpr c.2)
  have h2 := massShellTwoPointTubeWickHermiticity S hm hC hC_herm 2
    ![α c.1, α (P.mate c.1)] ![z c.1, z (P.mate c.1)] hz_pair hz_rev_pair
  change star (massShellTwoPointH m C 2 ![α c.1, α (P.mate c.1)] ![z c.1, z (P.mate c.1)]) =
    ∑ γ : Fin 2 → ι, (∏ i : Fin 2, S.C (![α c.1, α (P.mate c.1)] i) (γ i)) *
      massShellTwoPointH m C 2 (γ ∘ Fin.rev)
        (fun k μ => star (![z c.1, z (P.mate c.1)] (Fin.rev k) μ)) at h2
  rw [h2, hz_rev_pair_eq]
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  rw [Fin.prod_univ_two]
  rfl

theorem wickMassShellOSHermiticity {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {m : ℝ} (hm : 0 < m) {η : ℂ} (hη : η = 1 ∨ η = -1)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q) :
    OSHermiticity S (wickMassShellS m hm η C hC) :=
  schwingerFromTube_os_hermiticity S (wickMassShellTubeExtension m hm η C hC)
    (wickMassShellTubeWickHermiticity S hm hη hC hC_herm)

theorem wickMassShellTubePCT {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) {η : ℂ} (hη : η = 1 ∨ η = -1)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q) :
    TubePCT η R (wickMassShellTubeExtension m hm η C hC) := by
  intro n α z hz
  change wickMassShellH m η C n α (-(z ∘ Fin.rev)) =
    η ^ (n * (n - 1) / 2) *
      ∑ β : Fin n → ι, (∏ i : Fin n, R.σ (-1, 1) (α i) (β i)) *
        wickMassShellH m η C n (β ∘ Fin.rev) z
  unfold wickMassShellH
  have h_rhs_swap :
      η ^ (n * (n - 1) / 2) *
        (∑ β : Fin n → ι, (∏ i : Fin n, R.σ (-1, 1) (α i) (β i)) *
          ∑ Q : ChordPairing n, η ^ Q.cross *
            ∏ c' : Q.Chord,
              massShellTwoPointH m C 2
                ![(β ∘ Fin.rev) c'.1, (β ∘ Fin.rev) (Q.mate c'.1)]
                ![z c'.1, z (Q.mate c'.1)]) =
      ∑ P : ChordPairing n, (η ^ (n * (n - 1) / 2) * η ^ P.rev.cross) *
        ∑ β : Fin n → ι, (∏ i : Fin n, R.σ (-1, 1) (α i) (β i)) *
          ∏ c : P.Chord,
            massShellTwoPointH m C 2 (![β c.1, β (P.mate c.1)] ∘ Fin.rev)
              ![z (Fin.rev (P.mate c.1)), z (Fin.rev c.1)] := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, ← (ChordPairing.revEquiv n).sum_comp]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    have hrevP : ChordPairing.revEquiv n P = P.rev := rfl
    rw [hrevP]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [← P.revChordEquiv.prod_comp]
    have h_prod_eq :
        (∏ c : P.Chord,
          massShellTwoPointH m C 2
            ![(β ∘ Fin.rev) (P.revChordEquiv c).1,
              (β ∘ Fin.rev) (P.rev.mate (P.revChordEquiv c).1)]
            ![z (P.revChordEquiv c).1, z (P.rev.mate (P.revChordEquiv c).1)]) =
        ∏ c : P.Chord,
          massShellTwoPointH m C 2 (![β c.1, β (P.mate c.1)] ∘ Fin.rev)
            ![z (Fin.rev (P.mate c.1)), z (Fin.rev c.1)] := by
      refine Finset.prod_congr rfl (fun c _ => ?_)
      have hm_eq : P.rev.mate (P.revChordEquiv c).1 = Fin.rev c.1 := by
        change Fin.rev (P.mate (Fin.rev (Fin.rev (P.mate c.1)))) = Fin.rev c.1
        rw [Fin.rev_rev, P.mate_mate]
      have h1 : (P.revChordEquiv c).1 = Fin.rev (P.mate c.1) := rfl
      have hβ : ![(β ∘ Fin.rev) (Fin.rev (P.mate c.1)), (β ∘ Fin.rev) (Fin.rev c.1)] =
          ![β c.1, β (P.mate c.1)] ∘ Fin.rev := by
        ext k
        fin_cases k <;> simp [Fin.rev_rev]
      rw [hm_eq, h1, hβ]
    rw [h_prod_eq]
    ring
  rw [h_rhs_swap]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [← P.eta_pow_card_chord_mul_cross hη,
      P.sum_prod_chord_factor (fun i b => R.σ (-1, 1) (α i) b)
        (fun c γ => massShellTwoPointH m C 2 (γ ∘ Fin.rev)
          ![z (Fin.rev (P.mate c.1)), z (Fin.rev c.1)])]
  have h_each : ∀ c : P.Chord,
      massShellTwoPointH m C 2 ![α c.1, α (P.mate c.1)]
        ![(-(z ∘ Fin.rev)) c.1, (-(z ∘ Fin.rev)) (P.mate c.1)] =
      η * ∑ γ : Fin 2 → ι,
        (R.σ (-1, 1) (α c.1) (γ 0) * R.σ (-1, 1) (α (P.mate c.1)) (γ 1)) *
          massShellTwoPointH m C 2 (γ ∘ Fin.rev)
            ![z (Fin.rev (P.mate c.1)), z (Fin.rev c.1)] := by
    intro c
    let w : Fin 2 → Fin 4 → ℂ := ![z (Fin.rev (P.mate c.1)), z (Fin.rev c.1)]
    have hw : w ∈ forward_tube_n 2 := pair_mem_forward_tube_two hz (Fin.rev_lt_rev.mpr c.2)
    have h_neg_w : ![(-(z ∘ Fin.rev)) c.1, (-(z ∘ Fin.rev)) (P.mate c.1)] = -(w ∘ Fin.rev) := by
      ext k μ
      fin_cases k <;> rfl
    have h2 := massShellTwoPointTubePCT R hm hC hC_pct 2 ![α c.1, α (P.mate c.1)] w hw
    rw [two_mul_two_sub_one_div_two, pow_one] at h2
    change massShellTwoPointH m C 2 ![α c.1, α (P.mate c.1)] (-(w ∘ Fin.rev)) =
      η * ∑ γ : Fin 2 → ι,
        (∏ i : Fin 2, R.σ (-1, 1) (![α c.1, α (P.mate c.1)] i) (γ i)) *
          massShellTwoPointH m C 2 (γ ∘ Fin.rev) w at h2
    rw [h_neg_w, h2]
    congr 1
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    rw [Fin.prod_univ_two]
    rfl
  simp_rw [h_each, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  ring

theorem wickMassShellWightmanPCT {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) {η : ℂ} (hη : η = 1 ∨ η = -1)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q) :
    WightmanPCT η R (wickMassShellW m η C hC) :=
  wightman_pct_of_tubePCT_general R (wickMassShellW m η C hC)
    (wickMassShellTubeExtension m hm η C hC)
    (wickMassShellTubePCT R hm hη hC hC_pct)
    (wickMassShellTubeTranslationInvariant hm η hC)

theorem wickMassShellWeakLocality {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) {η : ℂ} (hη : η = 1 ∨ η = -1)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R.rep A (α i) (β i)) * C β q)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q) :
    WeakLocality η (wickMassShellW m η C hC) :=
  weakLocality_of_tubePCT R (wickMassShellW m η C hC)
    (wickMassShellTubeExtension m hm η C hC)
    (wickMassShellTubeCovariant R hm η hC hC_cov)
    (wickMassShellTubePCT R hm hη hC hC_pct)

noncomputable def freeKGW (m : ℝ) (hm : 0 < m) : WightmanFamily Unit :=
  wickMassShellW m 1 massiveKGCoeff (massiveKGCoeff_data hm)

noncomputable def freeKGTubeExtension (m : ℝ) (hm : 0 < m) :
    TubeExtension (freeKGW m hm) :=
  wickMassShellTubeExtension m hm 1 massiveKGCoeff (massiveKGCoeff_data hm)

noncomputable def freeKGS (m : ℝ) (hm : 0 < m) : SchwingerFamily Unit :=
  wickMassShellS m hm 1 massiveKGCoeff (massiveKGCoeff_data hm)

theorem freeKG_forwardConeSpectrumCondition {m : ℝ} (hm : 0 < m) :
    ForwardConeSpectrumCondition (freeKGW m hm) :=
  wickMassShell_forwardConeSpectrumCondition hm 1 (massiveKGCoeff_data hm)

theorem freeKGW_twoPoint_ne_zero {m : ℝ} (hm : 0 < m) :
    freeKGW m hm 2 default ≠ 0 :=
  (wickMassShell_nondeg_and_not_zeroMomentum hm 1 (massiveKGCoeff_data hm) default
    continuous_const (fun _ => zero_lt_one) (fun _ => Complex.ofReal_one.symm)).1

theorem not_zeroMomentumSpectrumCondition_freeKGW {m : ℝ} (hm : 0 < m) :
    ¬ ZeroMomentumSpectrumCondition (freeKGW m hm) :=
  (wickMassShell_nondeg_and_not_zeroMomentum hm 1 (massiveKGCoeff_data hm) default
    continuous_const (fun _ => zero_lt_one) (fun _ => Complex.ofReal_one.symm)).2

theorem freeKGTubeTranslationInvariant {m : ℝ} (hm : 0 < m) :
    TubeTranslationInvariant (freeKGTubeExtension m hm) :=
  wickMassShellTubeTranslationInvariant hm 1 (massiveKGCoeff_data hm)

theorem freeKGOSTranslationInvariant {m : ℝ} (hm : 0 < m) :
    OSTranslationInvariant (freeKGS m hm) :=
  wickMassShellOSTranslationInvariant hm 1 (massiveKGCoeff_data hm)

theorem freeKGTubeCovariant {m : ℝ} (hm : 0 < m) :
    TubeCovariant trivialRep (freeKGTubeExtension m hm) :=
  wickMassShellTubeCovariant trivialRep hm 1 (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])

theorem freeKGPoincareCovariant {m : ℝ} (hm : 0 < m) :
    PoincareCovariant trivialRep (freeKGW m hm) :=
  wickMassShellPoincareCovariant trivialRep hm 1 (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])

theorem freeKGTubeWickHermiticity {m : ℝ} (hm : 0 < m) :
    TubeWickHermiticity trivialStarStructure (freeKGTubeExtension m hm) :=
  wickMassShellTubeWickHermiticity trivialStarStructure hm (Or.inl rfl) (massiveKGCoeff_data hm)
    (fun _ _ => by simp [massiveKGCoeff, trivialStarStructure])

theorem freeKGOSHermiticity {m : ℝ} (hm : 0 < m) :
    OSHermiticity trivialStarStructure (freeKGS m hm) :=
  wickMassShellOSHermiticity trivialStarStructure hm (Or.inl rfl) (massiveKGCoeff_data hm)
    (fun _ _ => by simp [massiveKGCoeff, trivialStarStructure])

theorem freeKGTubePCT {m : ℝ} (hm : 0 < m) :
    TubePCT 1 trivialRep (freeKGTubeExtension m hm) :=
  wickMassShellTubePCT trivialRep hm (Or.inl rfl) (massiveKGCoeff_data hm)
    (fun _ _ => by simp [massiveKGCoeff, trivialRep])

theorem freeKGWightmanPCT {m : ℝ} (hm : 0 < m) :
    WightmanPCT 1 trivialRep (freeKGW m hm) :=
  wickMassShellWightmanPCT trivialRep hm (Or.inl rfl) (massiveKGCoeff_data hm)
    (fun _ _ => by simp [massiveKGCoeff, trivialRep])

theorem freeKGWeakLocality {m : ℝ} (hm : 0 < m) :
    WeakLocality 1 (freeKGW m hm) :=
  wickMassShellWeakLocality trivialRep hm (Or.inl rfl) (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])
    (fun _ _ => by simp [massiveKGCoeff, trivialRep])

theorem freeKG_spin_statistics {m : ℝ} (hm : 0 < m) {η : ℂ}
    (hloc : WeakLocality η (freeKGW m hm)) :
    η = 1 :=
  spin_statistics_of_tubePCT_and_weakLocality trivialRep (freeKGW m hm)
    (freeKGTubeExtension m hm) (freeKGTubeCovariant hm) (freeKGTubePCT hm)
    hloc ⟨default, freeKGW_twoPoint_ne_zero hm⟩

noncomputable def freeDiracW (m : ℝ) (hm : 0 < m) :
    WightmanFamily (Fin 2 ⊕ Fin 2) :=
  wickMassShellW m (-1) (diracMassShellCoeff m) (diracMassShellCoeff_data hm)

noncomputable def freeDiracTubeExtension (m : ℝ) (hm : 0 < m) :
    TubeExtension (freeDiracW m hm) :=
  wickMassShellTubeExtension m hm (-1) (diracMassShellCoeff m) (diracMassShellCoeff_data hm)

noncomputable def freeDiracS (m : ℝ) (hm : 0 < m) :
    SchwingerFamily (Fin 2 ⊕ Fin 2) :=
  wickMassShellS m hm (-1) (diracMassShellCoeff m) (diracMassShellCoeff_data hm)

theorem freeDirac_forwardConeSpectrumCondition {m : ℝ} (hm : 0 < m) :
    ForwardConeSpectrumCondition (freeDiracW m hm) :=
  wickMassShell_forwardConeSpectrumCondition hm (-1) (diracMassShellCoeff_data hm)

theorem freeDiracW_twoPoint_inl_inr_zero_ne_zero {m : ℝ} (hm : 0 < m) :
    freeDiracW m hm 2 ![Sum.inl 0, Sum.inr 0] ≠ 0 := by
  refine (wickMassShell_nondeg_and_not_zeroMomentum hm (-1)
    (diracMassShellCoeff_data hm) ![Sum.inl 0, Sum.inr 0]
    ((continuous_massShellEnergy m).add (continuous_apply 2))
    (massShellEnergy_add_third_pos hm) (fun p => ?_)).1
  simp [diracMassShellCoeff, massShellVec]

theorem freeDiracW_twoPoint_nondegenerate {m : ℝ} (hm : 0 < m) :
    ∃ β : Fin 2 → Fin 2 ⊕ Fin 2, freeDiracW m hm 2 β ≠ 0 :=
  ⟨![Sum.inl 0, Sum.inr 0], freeDiracW_twoPoint_inl_inr_zero_ne_zero hm⟩

theorem not_zeroMomentumSpectrumCondition_freeDiracW {m : ℝ} (hm : 0 < m) :
    ¬ ZeroMomentumSpectrumCondition (freeDiracW m hm) := by
  refine (wickMassShell_nondeg_and_not_zeroMomentum hm (-1)
    (diracMassShellCoeff_data hm) ![Sum.inl 0, Sum.inr 0]
    ((continuous_massShellEnergy m).add (continuous_apply 2))
    (massShellEnergy_add_third_pos hm) (fun p => ?_)).2
  simp [diracMassShellCoeff, massShellVec]

theorem freeDiracTubeTranslationInvariant {m : ℝ} (hm : 0 < m) :
    TubeTranslationInvariant (freeDiracTubeExtension m hm) :=
  wickMassShellTubeTranslationInvariant hm (-1) (diracMassShellCoeff_data hm)

theorem freeDiracOSTranslationInvariant {m : ℝ} (hm : 0 < m) :
    OSTranslationInvariant (freeDiracS m hm) :=
  wickMassShellOSTranslationInvariant hm (-1) (diracMassShellCoeff_data hm)

theorem freeDiracTubeCovariant {m : ℝ} (hm : 0 < m) :
    TubeCovariant diracRep (freeDiracTubeExtension m hm) :=
  wickMassShellTubeCovariant diracRep hm (-1) (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_lorentz m)

theorem freeDiracPoincareCovariant {m : ℝ} (hm : 0 < m) :
    PoincareCovariant diracRep (freeDiracW m hm) :=
  wickMassShellPoincareCovariant diracRep hm (-1) (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_lorentz m)

theorem freeDiracTubeWickHermiticity {m : ℝ} (hm : 0 < m) :
    TubeWickHermiticity diracStarStructure (freeDiracTubeExtension m hm) :=
  wickMassShellTubeWickHermiticity diracStarStructure hm (Or.inr rfl)
    (diracMassShellCoeff_data hm) (diracMassShellCoeff_herm m)

theorem freeDiracOSHermiticity {m : ℝ} (hm : 0 < m) :
    OSHermiticity diracStarStructure (freeDiracS m hm) :=
  wickMassShellOSHermiticity diracStarStructure hm (Or.inr rfl)
    (diracMassShellCoeff_data hm) (diracMassShellCoeff_herm m)

theorem freeDiracTubePCT {m : ℝ} (hm : 0 < m) :
    TubePCT (-1) diracRep (freeDiracTubeExtension m hm) :=
  wickMassShellTubePCT diracRep hm (Or.inr rfl)
    (diracMassShellCoeff_data hm) (diracMassShellCoeff_pct m)

theorem freeDiracWightmanPCT {m : ℝ} (hm : 0 < m) :
    WightmanPCT (-1) diracRep (freeDiracW m hm) :=
  wickMassShellWightmanPCT diracRep hm (Or.inr rfl)
    (diracMassShellCoeff_data hm) (diracMassShellCoeff_pct m)

theorem freeDiracWeakLocality {m : ℝ} (hm : 0 < m) :
    WeakLocality (-1) (freeDiracW m hm) :=
  wickMassShellWeakLocality diracRep hm (Or.inr rfl)
    (diracMassShellCoeff_data hm) (diracMassShellCoeff_lorentz m) (diracMassShellCoeff_pct m)

theorem freeDirac_spin_statistics {m : ℝ} (hm : 0 < m) {η : ℂ}
    (hloc : WeakLocality η (freeDiracW m hm)) :
    η = -1 :=
  spin_statistics_of_tubePCT_and_weakLocality diracRep (freeDiracW m hm)
    (freeDiracTubeExtension m hm) (freeDiracTubeCovariant hm) (freeDiracTubePCT hm)
    hloc (freeDiracW_twoPoint_nondegenerate hm)

end

end QFT
