import OSReconstruction

namespace QFT

open Geometry Geometry.MatrixAnalysis Geometry.PolarDecomposition
  MeasureTheory Filter Topology Matrix
open scoped ComplexOrder FourierTransform RealInnerProductSpace
  Interval ContDiff InnerProductSpace

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def vacS : SchwingerFamily ι
  | 0, _, _ => 1
  | _ + 1, _, _ => 0

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma vacS_zero (α : Fin 0 → ι) (x : Fin 0 → Fin 4 → ℝ) :
    vacS 0 α x = 1 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma vacS_succ (n : ℕ) (α : Fin (n + 1) → ι) (x : Fin (n + 1) → Fin 4 → ℝ) :
    vacS (n + 1) α x = 0 := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma vacS_of_one_le {n : ℕ} (hn : 1 ≤ n) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ) :
    vacS n α x = 0 := by
  cases n with
  | zero => omega
  | succ m => rfl

omit [Fintype ι] [DecidableEq ι] in
theorem vacS_vacuumNormalized : OSVacuumNormalized (vacS (ι := ι)) := rfl

noncomputable def vacW : WightmanFamily ι
  | 0, _ => TemperedDistribution.delta (0 : Fin 0 → Fin 4 → ℝ)
  | _ + 1, _ => 0

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma vacW_zero_apply (α : Fin 0 → ι) (f : SchwartzMap (Fin 0 → Fin 4 → ℝ) ℂ) :
    vacW 0 α f = f 0 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma vacW_succ (n : ℕ) (α : Fin (n + 1) → ι) :
    vacW (n + 1) α = 0 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma vacW_succ_apply (n : ℕ) (α : Fin (n + 1) → ι)
    (f : SchwartzMap (Fin (n + 1) → Fin 4 → ℝ) ℂ) :
    vacW (n + 1) α f = 0 := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma vacW_of_one_le {n : ℕ} (hn : 1 ≤ n) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    vacW n α f = 0 := by
  cases n with
  | zero => omega
  | succ m => rfl

def vacH : ∀ n : ℕ, (Fin n → ι) → (Fin n → Fin 4 → ℂ) → ℂ
  | 0, _, _ => 1
  | _ + 1, _, _ => 0

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma vacH_zero (α : Fin 0 → ι) (z : Fin 0 → Fin 4 → ℂ) :
    vacH 0 α z = 1 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma vacH_succ (n : ℕ) (α : Fin (n + 1) → ι) (z : Fin (n + 1) → Fin 4 → ℂ) :
    vacH (n + 1) α z = 0 := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma vacH_of_one_le {n : ℕ} (hn : 1 ≤ n) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ) :
    vacH n α z = 0 := by
  cases n with
  | zero => omega
  | succ m => rfl

lemma volume_fin0_eq_dirac :
    (volume : Measure (Fin 0 → Fin 4 → ℝ)) = Measure.dirac 0 := by
  rw [volume_pi, Measure.pi_of_empty]
  congr 1
  exact Subsingleton.elim _ _

@[simp]
lemma integral_fin0 (g : (Fin 0 → Fin 4 → ℝ) → ℂ) :
    (∫ x : Fin 0 → Fin 4 → ℝ, g x) = g 0 := by
  rw [volume_fin0_eq_dirac, integral_dirac]

omit [Fintype ι] [DecidableEq ι] in
noncomputable def vacTubeExtension : TubeExtension (vacW (ι := ι)) where
  H := vacH
  analytic n α := by
    cases n with
    | zero => exact analyticOn_const
    | succ m => exact analyticOn_const
  boundary n α f v _hv := by
    cases n with
    | zero =>
      have h_eq : (fun t : ℝ => ∫ x : Fin 0 → Fin 4 → ℝ,
          vacH 0 α (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x) =
          fun _ : ℝ => vacW 0 α f := by
        ext t
        simp [vacH_zero, vacW_zero_apply]
      rw [h_eq]
      exact tendsto_const_nhds
    | succ m =>
      have h_eq : (fun t : ℝ => ∫ x : Fin (m + 1) → Fin 4 → ℝ,
          vacH (m + 1) α
            (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x) =
          fun _ : ℝ => vacW (m + 1) α f := by
        ext t
        simp [vacH_succ]
      rw [h_eq]
      exact tendsto_const_nhds

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma vacTubeExtension_H : (vacTubeExtension (ι := ι)).H = vacH := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem schwingerFromTube_vacTubeExtension :
    schwingerFromTube (vacTubeExtension (ι := ι)) = vacS := by
  ext n α x
  cases n <;> rfl

omit [Fintype ι] [DecidableEq ι] in
theorem vacTubeTranslationInvariant :
    TubeTranslationInvariant (vacTubeExtension (ι := ι)) := by
  intro n α z a _hz
  cases n <;> rfl

theorem vacTubeComplexCovariant (R : HolomorphicLorentzRep ι) :
    ComplexCovariant R (vacTubeExtension (ι := ι)) := by
  intro n A B z _hz _hAz α
  cases n with
  | zero =>
    have hα : α = Fin.elim0 := Subsingleton.elim _ _
    subst hα
    simp [vacTubeExtension_H, vacH_zero]
  | succ m =>
    simp [vacTubeExtension_H, vacH_succ]

theorem vacTubeCovariant (R : HolomorphicLorentzRep ι) :
    TubeCovariant R (vacTubeExtension (ι := ι)) := by
  intro n A z hz hAz α
  exact vacTubeComplexCovariant R n A (sl2c_conj A) z hz hAz α

theorem vacTubeWickHermiticity {R : HolomorphicLorentzRep ι} (S : StarStructure R) :
    TubeWickHermiticity S (vacTubeExtension (ι := ι)) := by
  intro n α z _hz _hstar
  cases n with
  | zero =>
    have hα : α = Fin.elim0 := Subsingleton.elim _ _
    subst hα
    simp [vacTubeExtension_H, vacH_zero]
  | succ m =>
    simp [vacTubeExtension_H, vacH_succ]

omit [Fintype ι] [DecidableEq ι] in
theorem vacTubeWeakLocality (η : ℂ) :
    TubeWeakLocality η (vacTubeExtension (ι := ι)) := by
  intro n α z _hz
  cases n with
  | zero =>
    simp [vacTubeExtension_H, vacH_zero]
  | succ m =>
    simp [vacTubeExtension_H, vacH_succ]

theorem vacTubePCT (R : HolomorphicLorentzRep ι) (η : ℂ) :
    TubePCT η R (vacTubeExtension (ι := ι)) := by
  intro n α z _hz
  cases n with
  | zero =>
    simp [vacTubeExtension_H, vacH_zero]
  | succ m =>
    simp [vacTubeExtension_H, vacH_succ]

omit [Fintype ι] [DecidableEq ι] in
lemma osConfig_eq_osVacuumConfig_iff (A : OSConfig ι) :
    A = osVacuumConfig ι ↔ A.1 = 0 := by
  refine ⟨fun h => h ▸ rfl, osConfig_eq_osVacuumConfig_of_fst_eq_zero⟩

open Classical in
theorem osKernel_vacS {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (A B : OSConfig ι) :
    osKernel S vacS A B =
      if A = osVacuumConfig ι ∧ B = osVacuumConfig ι then 1 else 0 := by
  by_cases h : A = osVacuumConfig ι ∧ B = osVacuumConfig ι
  · rw [if_pos h, h.1, h.2]
    dsimp [osKernel, osVacuumConfig]
    simp
  · rw [if_neg h]
    have h_pos : 1 ≤ A.1 + B.1 := by
      by_contra hc
      have hA0 : A.1 = 0 := by omega
      have hB0 : B.1 = 0 := by omega
      exact h ⟨osConfig_eq_osVacuumConfig_of_fst_eq_zero hA0,
        osConfig_eq_osVacuumConfig_of_fst_eq_zero hB0⟩
    unfold osKernel
    refine Finset.sum_eq_zero (fun β _ => ?_)
    rw [vacS_of_one_le h_pos, mul_zero]

@[simp]
lemma osKernel_vacS_osVacuumConfig_self {R : HolomorphicLorentzRep ι} (S : StarStructure R) :
    osKernel S vacS (osVacuumConfig ι) (osVacuumConfig ι) = 1 := by
  classical
  rw [osKernel_vacS, if_pos ⟨rfl, rfl⟩]

open Classical in
lemma osKernel_vacS_osVacuumConfig_left {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (B : OSConfig ι) :
    osKernel S vacS (osVacuumConfig ι) B =
      if B = osVacuumConfig ι then 1 else 0 := by
  rw [osKernel_vacS]
  by_cases hB : B = osVacuumConfig ι <;> simp [hB]

open Classical in
lemma osKernel_vacS_osVacuumConfig_right {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (A : OSConfig ι) :
    osKernel S vacS A (osVacuumConfig ι) =
      if A = osVacuumConfig ι then 1 else 0 := by
  rw [osKernel_vacS]
  by_cases hA : A = osVacuumConfig ι <;> simp [hA]

lemma osKernel_vacS_factor {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (A B : OSConfig ι) :
    osKernel S vacS A B =
      osKernel S vacS A (osVacuumConfig ι) *
        osKernel S vacS (osVacuumConfig ι) B := by
  classical
  rw [osKernel_vacS, osKernel_vacS_osVacuumConfig_right, osKernel_vacS_osVacuumConfig_left]
  by_cases hA : A = osVacuumConfig ι <;> by_cases hB : B = osVacuumConfig ι <;>
    simp [hA, hB]

theorem osPreInner_vacS {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (Ψ Φ : OSConfig ι →₀ ℂ) :
    osPreInner S vacS Ψ Φ =
      star (Ψ (osVacuumConfig ι)) * Φ (osVacuumConfig ι) := by
  classical
  unfold osPreInner
  have h_inner : ∀ (A : OSConfig ι) (cA : ℂ),
      (Φ.sum fun B cB => star cA * cB * osKernel S vacS A B) =
        if A = osVacuumConfig ι then star cA * Φ (osVacuumConfig ι) else 0 := by
    intro A cA
    by_cases hA : A = osVacuumConfig ι
    · subst hA
      rw [if_pos rfl, Finsupp.sum]
      have h_term : ∀ B ∈ Φ.support,
          star cA * Φ B * osKernel S vacS (osVacuumConfig ι) B =
            if B = osVacuumConfig ι then star cA * Φ (osVacuumConfig ι) else 0 := by
        intro B _
        rw [osKernel_vacS_osVacuumConfig_left]
        split_ifs with hB
        · subst hB; ring
        · ring
      rw [Finset.sum_congr rfl h_term, Finset.sum_ite_eq']
      split_ifs with hmem
      · rfl
      · rw [Finsupp.notMem_support_iff.mp hmem, mul_zero]
    · rw [if_neg hA, Finsupp.sum]
      refine Finset.sum_eq_zero (fun B _ => ?_)
      rw [osKernel_vacS, if_neg (fun h => hA h.1), mul_zero]
  rw [Finsupp.sum, Finset.sum_congr rfl (fun A _ => h_inner A (Ψ A)), Finset.sum_ite_eq']
  split_ifs with hmem
  · rfl
  · rw [Finsupp.notMem_support_iff.mp hmem, star_zero, zero_mul]

theorem vacOSReflectionPositive {R : HolomorphicLorentzRep ι} (S : StarStructure R) :
    OSReflectionPositive S vacS := by
  intro Ψ
  rw [osPreInner_vacS, mul_comm]
  change (Ψ (osVacuumConfig ι) * (starRingEnd ℂ) (Ψ (osVacuumConfig ι))).re ≥ 0
  rw [Complex.mul_conj, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

theorem vacOSAxioms (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) :
    OSAxioms R S η vacS := by
  rw [← schwingerFromTube_vacTubeExtension]
  refine schwingerFromTube_osAxioms R S vacW vacTubeExtension
    vacTubeTranslationInvariant (vacTubeCovariant R)
    (vacTubeWickHermiticity S) (vacTubePCT R η) ?_
  rw [schwingerFromTube_vacTubeExtension]
  exact vacOSReflectionPositive S

def vacOSData (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    OSReflectionPositiveData R S :=
  (vacOSAxioms R S 1).toReflectionPositiveData

@[simp]
lemma vacOSData_𝒮 (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    (vacOSData R S).𝒮 = vacS := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem vacOSTranslationInvariant : OSTranslationInvariant (vacS (ι := ι)) := by
  intro n α x _hx a
  cases n <;> rfl

theorem vacOSTimeCluster (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    OSTimeClusterDecomposition (vacOSData R S) := by
  classical
  intro A B
  have h_const : (fun τ : ℝ =>
      osKernel S (vacOSData R S).𝒮 A
        (osConfigTimeShift (max τ 0) (le_max_right τ 0) B)) =
      fun _ : ℝ =>
        osKernel S (vacOSData R S).𝒮 A (osVacuumConfig ι) *
          osKernel S (vacOSData R S).𝒮 (osVacuumConfig ι) B := by
    ext τ
    change osKernel S vacS A (osConfigTimeShift (max τ 0) (le_max_right τ 0) B) =
      osKernel S vacS A (osVacuumConfig ι) * osKernel S vacS (osVacuumConfig ι) B
    rw [← osKernel_vacS_factor S A B, osKernel_vacS, osKernel_vacS]
    have hB : osConfigTimeShift (max τ 0) (le_max_right τ 0) B = osVacuumConfig ι ↔
        B = osVacuumConfig ι := by
      rw [osConfig_eq_osVacuumConfig_iff, osConfig_eq_osVacuumConfig_iff]
      rfl
    simp [hB]
  rw [h_const]
  exact tendsto_const_nhds

theorem vacOSSpatialClusterAlong (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (a : Fin 3 → ℝ) :
    OSSpatialClusterAlong (vacOSData R S) a := by
  classical
  intro A B
  have h_const : (fun t : ℝ =>
      osKernel S (vacOSData R S).𝒮 A (osConfigSpatialShift (t • a) B)) =
      fun _ : ℝ =>
        osKernel S (vacOSData R S).𝒮 A (osVacuumConfig ι) *
          osKernel S (vacOSData R S).𝒮 (osVacuumConfig ι) B := by
    ext t
    change osKernel S vacS A (osConfigSpatialShift (t • a) B) =
      osKernel S vacS A (osVacuumConfig ι) * osKernel S vacS (osVacuumConfig ι) B
    rw [← osKernel_vacS_factor S A B, osKernel_vacS, osKernel_vacS]
    have hB : osConfigSpatialShift (t • a) B = osVacuumConfig ι ↔
        B = osVacuumConfig ι := by
      rw [osConfig_eq_osVacuumConfig_iff, osConfig_eq_osVacuumConfig_iff]
      rfl
    simp [hB]
  rw [h_const]
  exact tendsto_const_nhds

theorem vacOSSpatialCluster (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    OSSpatialClusterDecomposition (vacOSData R S) :=
  fun a _ha => vacOSSpatialClusterAlong R S a

theorem vacOSContraction (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    OSContractionCondition (vacOSData R S) :=
  osContractionCondition_of_timeCluster (vacOSData R S)
    vacOSTranslationInvariant (vacOSTimeCluster R S)

theorem vacHilbert_eq_smul_osVacuum (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (Φ : OSHilbert (vacOSData R S)) :
    Φ = ⟪osVacuum (vacOSData R S), Φ⟫_ℂ • osVacuum (vacOSData R S) :=
  eq_smul_osVacuum_of_twoPoint_eq_zero (vacOSData R S)
    vacOSTranslationInvariant vacS_vacuumNormalized (fun _ _ _ => rfl) Φ

lemma vacHilbert_clm_eq_id_of_map_vacuum (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (L : OSHilbert (vacOSData R S) →L[ℂ] OSHilbert (vacOSData R S))
    (hL : L (osVacuum (vacOSData R S)) = osVacuum (vacOSData R S)) :
    L = ContinuousLinearMap.id ℂ (OSHilbert (vacOSData R S)) := by
  ext x
  rw [vacHilbert_eq_smul_osVacuum R S x, map_smul, hL, ContinuousLinearMap.id_apply]

@[simp]
theorem vacOSContractionSemigroup_eq_id (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (hcontr : OSContractionCondition (vacOSData R S)) (τ : ℝ) (hτ : 0 ≤ τ) :
    osContractionSemigroup (vacOSData R S) hcontr τ hτ =
      ContinuousLinearMap.id ℂ (OSHilbert (vacOSData R S)) :=
  vacHilbert_clm_eq_id_of_map_vacuum R S _
    (osContractionSemigroup_vacuum (vacOSData R S) hcontr τ hτ)

@[simp]
theorem vacOSSpatialTranslate_eq_id (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (htrans : OSTranslationInvariant (vacOSData R S).𝒮) (a : Fin 3 → ℝ) :
    osSpatialTranslate (vacOSData R S) htrans a =
      ContinuousLinearMap.id ℂ (OSHilbert (vacOSData R S)) :=
  vacHilbert_clm_eq_id_of_map_vacuum R S _
    (osSpatialTranslate_vacuum (vacOSData R S) htrans a)

def vacHolomorphicSemigroup (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    OSHolomorphicSemigroup (vacOSData R S) (vacOSContraction R S) where
  Z _ _ := ContinuousLinearMap.id ℂ (OSHilbert (vacOSData R S))
  real_eq τ hτ := (vacOSContractionSemigroup_eq_id R S (vacOSContraction R S) τ hτ).symm
  map_add _ _ _ _ := (ContinuousLinearMap.id_comp _).symm
  vacuum _ _ := rfl
  contraction _ _ _ := le_rfl
  adjoint_symm _ _ _ _ := rfl
  comm_spatial _ _ _ _ := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma minkowskiFourier_fin0 (f : SchwartzMap (Fin 0 → Fin 4 → ℝ) ℂ)
    (p : Fin 0 → Fin 4 → ℝ) :
    minkowskiFourier f p = f 0 := by
  unfold minkowskiFourier
  simp

omit [Fintype ι] [DecidableEq ι] in
theorem vacZeroMomentumSpectrumCondition : ZeroMomentumSpectrumCondition (vacW (ι := ι)) := by
  intro n α f h0
  cases n with
  | zero =>
    rw [vacW_zero_apply]
    rwa [minkowskiFourier_fin0] at h0
  | succ m =>
    exact vacW_succ_apply m α f

theorem vacPoincareCovariant (R : HolomorphicLorentzRep ι) :
    PoincareCovariant R (vacW (ι := ι)) := by
  intro n a A f f' hf α
  cases n with
  | zero =>
    have hα : α = Fin.elim0 := Subsingleton.elim _ _
    subst hα
    simp only [vacW_zero_apply, Fin.prod_univ_zero, one_mul, Fintype.sum_unique]
    have h0 := hf 0
    have h_act : (fun i : Fin 0 => poincareAct a A ((0 : Fin 0 → Fin 4 → ℝ) i)) = 0 :=
      Subsingleton.elim _ _
    rwa [h_act] at h0
  | succ m =>
    simp

omit [Fintype ι] [DecidableEq ι] in
theorem vacWeakLocality (η : ℂ) : WeakLocality η (vacW (ι := ι)) := by
  intro n α f f' _hsupp hrev
  cases n with
  | zero =>
    simp only [vacW_zero_apply, Nat.zero_mul, Nat.zero_div, pow_zero, one_mul]
    have h0 := hrev 0
    have h_eq : (fun i : Fin 0 => (0 : Fin 0 → Fin 4 → ℝ) (Fin.rev i)) = 0 :=
      Subsingleton.elim _ _
    rw [h_eq] at h0
    exact h0.symm
  | succ m =>
    simp

theorem vacPositivity {R : HolomorphicLorentzRep ι} (S : StarStructure R) :
    Positivity S (vacW (ι := ι)) := by
  intro N F G hG
  have h_outer : ∀ j ∈ Finset.range (N + 1),
      (∑ k ∈ Finset.range (N + 1),
        ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
          (∏ i, S.C (α i) (β i)) * vacW (j + k) (Fin.append (β ∘ Fin.rev) α') (G j k α α')) =
      if j = 0 then
        star (F 0 Fin.elim0 0) * F 0 Fin.elim0 0
      else 0 := by
    intro j _hj
    by_cases hj0 : j = 0
    · subst hj0
      rw [if_pos rfl]
      have h_inner : ∀ k ∈ Finset.range (N + 1),
          (∑ α : Fin 0 → ι, ∑ α' : Fin k → ι, ∑ β : Fin 0 → ι,
            (∏ i, S.C (α i) (β i)) *
              vacW (0 + k) (Fin.append (β ∘ Fin.rev) α') (G 0 k α α')) =
          if k = 0 then star (F 0 Fin.elim0 0) * F 0 Fin.elim0 0 else 0 := by
        intro k _hk
        by_cases hk0 : k = 0
        · subst hk0
          rw [if_pos rfl]
          simp only [Nat.add_zero, Fin.prod_univ_zero, one_mul,
            Fintype.sum_unique, vacW_zero_apply]
          have hG0 := hG 0 0 Fin.elim0 Fin.elim0 0
          have h1 : (fun i : Fin 0 => (0 : Fin 0 → Fin 4 → ℝ) (Fin.castAdd 0 (Fin.rev i))) = 0 :=
            Subsingleton.elim _ _
          have h2 : (fun i : Fin 0 => (0 : Fin 0 → Fin 4 → ℝ) (Fin.natAdd 0 i)) = 0 :=
            Subsingleton.elim _ _
          have h3 : (default : Fin 0 → ι) = Fin.elim0 := Subsingleton.elim _ _
          rw [h1, h2] at hG0
          rw [h3, hG0]
          rfl
        · rw [if_neg hk0]
          have hpos : 1 ≤ 0 + k := by omega
          refine Finset.sum_eq_zero (fun α _ => Finset.sum_eq_zero (fun α' _ =>
            Finset.sum_eq_zero (fun β _ => ?_)))
          rw [vacW_of_one_le hpos, mul_zero]
      rw [Finset.sum_congr rfl h_inner, Finset.sum_ite_eq']
      simp
    · rw [if_neg hj0]
      refine Finset.sum_eq_zero (fun k _ => Finset.sum_eq_zero (fun α _ =>
        Finset.sum_eq_zero (fun α' _ => Finset.sum_eq_zero (fun β _ => ?_))))
      have hpos : 1 ≤ j + k := by omega
      rw [vacW_of_one_le hpos, mul_zero]
  rw [Finset.sum_congr rfl h_outer, Finset.sum_ite_eq']
  simp only [Finset.mem_range, Nat.zero_lt_succ, ↓reduceIte]
  rw [mul_comm]
  change (0 : ℂ) ≤ (F 0 Fin.elim0 0) * (starRingEnd ℂ) (F 0 Fin.elim0 0)
  rw [Complex.mul_conj]
  exact_mod_cast Complex.normSq_nonneg _

noncomputable def vacOSReconstructedWightman
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) :
    OSReconstructedWightman R S η vacS where
  osAxioms := vacOSAxioms R S η
  contraction := vacOSContraction R S
  semigroup := vacHolomorphicSemigroup R S
  W := vacW
  E := vacTubeExtension
  schwinger_eq n α x _ := by rw [schwingerFromTube_vacTubeExtension]
  tube_covariant := vacTubeCovariant R
  tube_pct := vacTubePCT R η
  spectrum := vacZeroMomentumSpectrumCondition
  poincare := vacPoincareCovariant R
  weakLocality := vacWeakLocality η
  positivity := vacPositivity S

theorem vacOSReconstructedWightman_nonempty
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) :
    Nonempty (OSReconstructedWightman R S η vacS) :=
  ⟨vacOSReconstructedWightman R S η⟩

noncomputable def scalarVacuumTheory (η : ℂ) :
    ScalarOSReconstructedWightman η vacS :=
  vacOSReconstructedWightman trivialRep trivialStarStructure η

noncomputable def vectorVacuumTheory (η : ℂ) :
    VectorOSReconstructedWightman η vacS :=
  vacOSReconstructedWightman stdRep stdStarStructure η

noncomputable def diracVacuumTheory (η : ℂ) :
    DiracOSReconstructedWightman η vacS :=
  vacOSReconstructedWightman diracRep diracStarStructure η

noncomputable def spinorTensorBispinorVacuumTheory (m₁ m₂ : ℕ) (η : ℂ) :
    SpinorTensorBispinorOSReconstructedWightman m₁ m₂ η vacS :=
  vacOSReconstructedWightman
    (directSumRep (spinorTensorRep m₁ m₂) (chiralSwapRep (spinorTensorRep m₁ m₂)))
    (spinorTensorBispinorStarStructure m₁ m₂) η

noncomputable def vacHilbertLinearIsometryEquiv
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    OSHilbert (vacOSData R S) ≃ₗᵢ[ℂ] ℂ where
  toFun Φ := ⟪osVacuum (vacOSData R S), Φ⟫_ℂ
  map_add' Φ₁ Φ₂ := inner_add_right _ Φ₁ Φ₂
  map_smul' c Φ := by simp
  invFun c := c • osVacuum (vacOSData R S)
  left_inv Φ := (vacHilbert_eq_smul_osVacuum R S Φ).symm
  right_inv c := by
    dsimp
    rw [inner_smul_right,
        inner_osVacuum_self_of_normalized (vacOSData R S) vacS_vacuumNormalized,
        mul_one]
  norm_map' Φ := by
    dsimp
    conv_rhs => rw [vacHilbert_eq_smul_osVacuum R S Φ]
    rw [norm_smul, norm_osVacuum_of_normalized (vacOSData R S) vacS_vacuumNormalized,
        mul_one]

@[simp]
theorem vacSpinorRot_eq_id (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (η : ℂ) (U : SU2) :
    (vacOSReconstructedWightman R S η).spinorRot U =
      ContinuousLinearMap.id ℂ (vacOSReconstructedWightman R S η).Hilbert :=
  vacHilbert_clm_eq_id_of_map_vacuum R S _
    ((vacOSReconstructedWightman R S η).spinorRot_vacuum U)

@[simp]
theorem vacSpacetimeTranslate_eq_id (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (η : ℂ) (a : Fin 4 → ℝ) :
    (vacOSReconstructedWightman R S η).semigroup.spacetimeTranslate
      (vacOSReconstructedWightman R S η).osAxioms.os1_translation a =
      ContinuousLinearMap.id ℂ (vacOSReconstructedWightman R S η).Hilbert :=
  vacHilbert_clm_eq_id_of_map_vacuum R S _
    ((vacOSReconstructedWightman R S η).semigroup.spacetimeTranslate_vacuum
      (vacOSReconstructedWightman R S η).osAxioms.os1_translation a)

@[simp]
theorem vacFieldPrependLM_toOSHilbert_eq_zero
    (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (α₀ : ι) (x₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0)
    (Ψ : OSPreHilbertSpace (vacOSData R S)) :
    toOSHilbert (vacOSData R S) (osFieldPrependLM (vacOSData R S) α₀ x₀ hx₀ Ψ) = 0 :=
  toOSHilbert_osFieldPrependLM_eq_zero_of_twoPoint_eq_zero (vacOSData R S)
    vacOSTranslationInvariant (fun _ _ _ => rfl) α₀ x₀ hx₀ Ψ

namespace OSReconstructedWightman

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

omit [Fintype ι] [DecidableEq ι] in
theorem schwinger_zero_eq_vacS_of_normalized
    (hnorm : OSVacuumNormalized 𝒮) (α : Fin 0 → ι) (x : Fin 0 → Fin 4 → ℝ) :
    𝒮 0 α x = vacS 0 α x := by
  have hα : α = Fin.elim0 := Subsingleton.elim _ _
  have hx : x = euclidOrderedBasePoint 0 := Subsingleton.elim _ _
  rw [hα, hx, vacS_zero]
  exact hnorm

theorem schwinger_eq_vacS_of_twoPoint_eq_zero
    (P : OSReconstructedWightman R S η 𝒮) (hnorm : OSVacuumNormalized 𝒮)
    (h2 : ∀ (β : Fin 2 → ι) (y : Fin 2 → Fin 4 → ℝ),
      y ∈ orderedEuclidN 2 → 𝒮 2 β y = 0)
    (n : ℕ) (α : Fin n → ι) {x : Fin n → Fin 4 → ℝ} (hx : x ∈ orderedEuclidN n) :
    𝒮 n α x = vacS n α x := by
  cases n with
  | zero => exact schwinger_zero_eq_vacS_of_normalized hnorm α x
  | succ m =>
    rw [vacS_succ]
    exact P.schwinger_eq_zero_of_twoPoint_eq_zero h2 (m + 1) (by omega) α hx

theorem schwinger_eq_vacS_iff_twoPoint_eq_zero
    (P : OSReconstructedWightman R S η 𝒮) (hnorm : OSVacuumNormalized 𝒮) :
    (∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = vacS n α x) ↔
    (∀ (β : Fin 2 → ι) (y : Fin 2 → Fin 4 → ℝ),
      y ∈ orderedEuclidN 2 → 𝒮 2 β y = 0) :=
  ⟨fun hall β y hy => hall 2 β y hy,
   fun h2 n α _x hx => P.schwinger_eq_vacS_of_twoPoint_eq_zero hnorm h2 n α hx⟩

theorem tube_H_eq_vacH_of_twoPoint_eq_zero
    (P : OSReconstructedWightman R S η 𝒮) (hnorm : OSVacuumNormalized 𝒮)
    (h2 : ∀ (β : Fin 2 → ι) (y : Fin 2 → Fin 4 → ℝ),
      y ∈ orderedEuclidN 2 → 𝒮 2 β y = 0)
    (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) :
    P.E.H n α z = vacH n α z := by
  refine tubeExtension_eq_of_schwingerFromTube_eq P.E vacTubeExtension ?_ n α z hz
  intro m β x hx
  rw [← P.schwinger_eq m β x hx, schwingerFromTube_vacTubeExtension]
  exact P.schwinger_eq_vacS_of_twoPoint_eq_zero hnorm h2 m β hx

theorem wightman_eq_vacW_of_twoPoint_eq_zero
    (P : OSReconstructedWightman R S η 𝒮) (hnorm : OSVacuumNormalized 𝒮)
    (h2 : ∀ (β : Fin 2 → ι) (y : Fin 2 → Fin 4 → ℝ),
      y ∈ orderedEuclidN 2 → 𝒮 2 β y = 0) :
    P.W = vacW := by
  apply wightman_eq_of_schwingerFromTube_eq_unconditional P.E vacTubeExtension
  intro n α x hx
  rw [← P.schwinger_eq n α x hx, schwingerFromTube_vacTubeExtension]
  exact P.schwinger_eq_vacS_of_twoPoint_eq_zero hnorm h2 n α hx

theorem wightman_eq_vacW_iff_twoPoint_wightman_eq_zero
    (P : OSReconstructedWightman R S η 𝒮) (hnorm : OSVacuumNormalized 𝒮)
    (hinj : TubeBoundaryInjective P.E) :
    P.W = vacW ↔
      ∀ (β : Fin 2 → ι) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), P.W 2 β f = 0 := by
  refine ⟨fun h β f => by rw [h]; rfl, fun hW2 => ?_⟩
  exact P.wightman_eq_vacW_of_twoPoint_eq_zero hnorm
    ((P.all_nPoint_eq_zero_of_wightman_twoPoint_eq_zero hinj hW2).1 2 (by omega))

end OSReconstructedWightman

def momentS (c : ℕ → ℂ) : SchwingerFamily ι :=
  fun n _ _ => c n

def momentH (c : ℕ → ℂ) : ∀ n : ℕ, (Fin n → ι) → (Fin n → Fin 4 → ℂ) → ℂ :=
  fun n _ _ => c n

noncomputable def schwartzIntegralCLM (n : ℕ) :
    TemperedDistribution (Fin n → Fin 4 → ℝ) ℂ :=
  SchwartzMap.integralCLM ℂ (volume : Measure (Fin n → Fin 4 → ℝ))

@[simp]
lemma schwartzIntegralCLM_apply (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    schwartzIntegralCLM n f = ∫ x : Fin n → Fin 4 → ℝ, f x := rfl

noncomputable def momentW (c : ℕ → ℂ) : WightmanFamily ι :=
  fun n _ => c n • schwartzIntegralCLM n

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma momentW_apply (c : ℕ → ℂ) (n : ℕ) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    momentW c n α f = c n * ∫ x : Fin n → Fin 4 → ℝ, f x := rfl

noncomputable def unitIntegralSchwartz (n : ℕ) : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
  invMinkowskiFourierCLM n (vladimirov_psi_schwartz n 1 Real.zero_lt_one 0)

@[simp]
theorem integral_unitIntegralSchwartz (n : ℕ) :
    (∫ x : Fin n → Fin 4 → ℝ, unitIntegralSchwartz n x) = 1 := by
  rw [← minkowskiFourier_eval_zero_n]
  exact vladimirov_fourier_eval_zero_n n 0

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem momentW_unitIntegralSchwartz (c : ℕ → ℂ) (n : ℕ) (α : Fin n → ι) :
    momentW (ι := ι) c n α (unitIntegralSchwartz n) = c n := by
  rw [momentW_apply, integral_unitIntegralSchwartz, mul_one]

lemma integral_poincareAct_eq (n : ℕ) (a : Fin 4 → ℝ) (A : SL2C)
    (g : (Fin n → Fin 4 → ℝ) → ℂ) :
    (∫ x : Fin n → Fin 4 → ℝ, g (fun i => poincareAct a A (x i))) =
      ∫ x : Fin n → Fin 4 → ℝ, g x := by
  have h_eq : (fun x : Fin n → Fin 4 → ℝ => g (fun i => poincareAct a A (x i))) =
      fun x => g (lorentzEquiv n A x + fun _ => a) := rfl
  rw [h_eq]
  have h_mp := measurePreserving_lorentzEquiv_n n A
  have h_emb := (lorentzEquiv n A).toHomeomorph.measurableEmbedding
  rw [h_mp.integral_comp h_emb (fun y => g (y + fun _ => a))]
  exact integral_add_right_eq_self g (fun _ => a)

noncomputable def momentTubeExtension (c : ℕ → ℂ) :
    TubeExtension (momentW (ι := ι) c) where
  H := momentH c
  analytic _ _ := analyticOn_const
  boundary n α f v _hv := by
    have h_eq : (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        momentH (ι := ι) c n α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x) =
        fun _ => c n * ∫ x : Fin n → Fin 4 → ℝ, f x := by
      ext t
      dsimp [momentH]
      exact integral_const_mul (c n) f
    rw [h_eq, momentW_apply]
    exact tendsto_const_nhds

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma momentTubeExtension_H (c : ℕ → ℂ) :
    (momentTubeExtension (ι := ι) c).H = momentH c := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem schwingerFromTube_momentTubeExtension (c : ℕ → ℂ) :
    schwingerFromTube (momentTubeExtension (ι := ι) c) = momentS c := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem momentTubeBoundaryInjective (c : ℕ → ℂ) :
    TubeBoundaryInjective (momentTubeExtension (ι := ι) c) := by
  intro n α hW _z _hz
  have h_unit := hW (unitIntegralSchwartz n)
  rwa [momentW_unitIntegralSchwartz] at h_unit

omit [Fintype ι] [DecidableEq ι] in
theorem momentTubeTranslationInvariant (c : ℕ → ℂ) :
    TubeTranslationInvariant (momentTubeExtension (ι := ι) c) :=
  fun _ _ _ _ _ => rfl

theorem momentTubeCovariant (c : ℕ → ℂ) :
    TubeCovariant trivialRep (momentTubeExtension (ι := Unit) c) := by
  intro n A z _hz _hAz α
  simp [momentTubeExtension_H, momentH, trivialRep, HolomorphicLorentzRep.rep_apply]

omit [Fintype ι] [DecidableEq ι] in
theorem momentTubeWeakLocality (c : ℕ → ℂ) :
    TubeWeakLocality 1 (momentTubeExtension (ι := ι) c) := by
  intro n α z _hz
  simp [momentTubeExtension_H, momentH]

theorem momentTubePCT (c : ℕ → ℂ) :
    TubePCT 1 trivialRep (momentTubeExtension (ι := Unit) c) := by
  intro n α z _hz
  simp [momentTubeExtension_H, momentH, trivialRep]

omit [Fintype ι] [DecidableEq ι] in
theorem momentZeroMomentumSpectrumCondition (c : ℕ → ℂ) :
    ZeroMomentumSpectrumCondition (momentW (ι := ι) c) := by
  intro n α f h0
  rw [minkowskiFourier_eval_zero_n] at h0
  rw [momentW_apply, h0, mul_zero]

theorem momentPoincareCovariant (c : ℕ → ℂ) :
    PoincareCovariant trivialRep (momentW (ι := Unit) c) := by
  rw [trivialRep_covariant_iff]
  intro n a A f f' hf' α
  rw [momentW_apply, momentW_apply]
  congr 1
  have h_f : (fun x : Fin n → Fin 4 → ℝ => f x) =
      fun x => f' (fun i => poincareAct a A (x i)) := by
    ext x
    exact (hf' x).symm
  rw [h_f, integral_poincareAct_eq]

omit [Fintype ι] [DecidableEq ι] in
theorem momentWeakLocality (c : ℕ → ℂ) :
    WeakLocality 1 (momentW (ι := ι) c) := by
  intro n α f f' _hf_jost hf'
  rw [one_pow, one_mul, momentW_apply, momentW_apply]
  congr 1
  have h_f : (fun x : Fin n → Fin 4 → ℝ => f x) =
      fun x => f' (fun i => x (Fin.rev i)) := by
    ext x
    exact (hf' x).symm
  rw [h_f, integral_comp_rev]

omit [Fintype ι] [DecidableEq ι] in
theorem momentOSTranslationInvariant (c : ℕ → ℂ) :
    OSTranslationInvariant (momentS (ι := ι) c) :=
  fun _ _ _ _ _ => rfl

def osConfigLen (A : OSConfig ι) : ℕ := A.1

lemma osKernel_momentS {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (c : ℕ → ℂ) (A B : OSConfig ι) :
    osKernel S (momentS c) A B =
      (∑ β : Fin A.1 → ι, (∏ i, S.C (A.2.1 i) (β i))) * c (A.1 + B.1) := by
  dsimp [osKernel, momentS]
  rw [Finset.sum_mul]

lemma osKernel_trivialStarStructure_momentS (c : ℕ → ℂ) (A B : OSConfig Unit) :
    osKernel trivialStarStructure (momentS c) A B = c (osConfigLen A + osConfigLen B) := by
  unfold osKernel momentS trivialStarStructure osConfigLen
  simp

theorem osBasis_eq_of_momentS {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {c : ℕ → ℂ} (D : OSReflectionPositiveData R S) (hD : D.𝒮 = momentS c)
    (A B : OSConfig ι) (hn : A.1 = B.1) (hα : HEq A.2.1 B.2.1) :
    osBasis D A = osBasis D B := by
  have h_sub : ‖osBasisPre D A - osBasisPre D B‖ = 0 := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ)]
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    simp only [inner_osBasisPre, hD, osKernel_momentS]
    rcases A with ⟨nA, αA, xA, hxA⟩
    rcases B with ⟨nB, αB, xB, hxB⟩
    dsimp at hn hα
    subst hn
    subst hα
    simp
  rw [← sub_eq_zero, ← norm_eq_zero]
  change ‖toOSHilbert D (osBasisPre D A) - toOSHilbert D (osBasisPre D B)‖ = 0
  rw [← map_sub, norm_toOSHilbert]
  exact h_sub

theorem momentOSContraction {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {c : ℕ → ℂ} (D : OSReflectionPositiveData R S) (hD : D.𝒮 = momentS c) :
    OSContractionCondition D := by
  intro τ hτ Ψ
  have h_inner := osPreHilbert_inner_map_eq_of_osBasisPre₂ D
    (osTimeShiftLM D τ hτ) LinearMap.id (fun A B => by
      unfold osTimeShiftLM
      rw [osLiftConfigMap_osBasisPre, osLiftConfigMap_osBasisPre, LinearMap.id_apply,
          LinearMap.id_apply, inner_osBasisPre, inner_osBasisPre, hD,
          osKernel_momentS, osKernel_momentS]
      rfl) Ψ Ψ
  have h_norm : ‖osTimeShiftLM D τ hτ Ψ‖ = ‖Ψ‖ := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), h_inner]
    rfl
  exact le_of_eq h_norm

@[simp]
theorem momentOSContractionSemigroup_eq_id {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {c : ℕ → ℂ} (D : OSReflectionPositiveData R S) (hD : D.𝒮 = momentS c)
    (hcontr : OSContractionCondition D) (τ : ℝ) (hτ : 0 ≤ τ) :
    osContractionSemigroup D hcontr τ hτ = ContinuousLinearMap.id ℂ (OSHilbert D) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change osContractionSemigroup D hcontr τ hτ (toOSHilbert D Ψ) = toOSHilbert D Ψ
    rw [osContractionSemigroup_toOSHilbert]
    conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D Ψ]
    conv_rhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D Ψ]
    rw [map_finsuppSum, map_finsuppSum, map_finsuppSum]
    refine Finsupp.sum_congr (fun A _ => ?_)
    rw [LinearMap.map_smul, (toOSHilbert D).map_smul, (toOSHilbert D).map_smul]
    congr 1
    unfold osTimeShiftLM
    rw [osLiftConfigMap_osBasisPre]
    exact osBasis_eq_of_momentS D hD (osConfigTimeShift τ hτ A) A rfl HEq.rfl

def momentHolomorphicSemigroup {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {c : ℕ → ℂ} (D : OSReflectionPositiveData R S) (hD : D.𝒮 = momentS c)
    (hcontr : OSContractionCondition D) :
    OSHolomorphicSemigroup D hcontr where
  Z _ _ := ContinuousLinearMap.id ℂ (OSHilbert D)
  real_eq τ hτ := (momentOSContractionSemigroup_eq_id D hD hcontr τ hτ).symm
  map_add _ _ _ _ := (ContinuousLinearMap.id_comp _).symm
  vacuum _ _ := rfl
  contraction _ _ _ := le_rfl
  adjoint_symm _ _ _ _ := rfl
  comm_spatial _ _ _ _ := rfl

def twoModeMoment (w₁ w₂ r₁ r₂ : ℝ) (n : ℕ) : ℂ :=
  ((w₁ * r₁ ^ n + w₂ * r₂ ^ n : ℝ) : ℂ)

lemma twoModeMoment_add (w₁ w₂ r₁ r₂ : ℝ) (j k : ℕ) :
    twoModeMoment w₁ w₂ r₁ r₂ (j + k) =
      (w₁ : ℂ) * ((r₁ : ℂ) ^ j * (r₁ : ℂ) ^ k) +
      (w₂ : ℂ) * ((r₂ : ℂ) ^ j * (r₂ : ℂ) ^ k) := by
  dsimp [twoModeMoment]
  rw [pow_add, pow_add]
  push_cast
  ring

lemma sum_star_mul_pow_eq_normSq {α : Type*} (s : Finset α) (f : α → ℂ) (d : α → ℕ) (μ : ℝ) :
    (∑ a ∈ s, ∑ b ∈ s, (starRingEnd ℂ) (f a) * f b * ((μ : ℂ) ^ (d a) * (μ : ℂ) ^ (d b))) =
      ((Complex.normSq (∑ a ∈ s, (μ : ℂ) ^ (d a) * f a) : ℝ) : ℂ) := by
  have h_term : ∀ a b : α,
      (starRingEnd ℂ) (f a) * f b * ((μ : ℂ) ^ (d a) * (μ : ℂ) ^ (d b)) =
        (starRingEnd ℂ) ((μ : ℂ) ^ (d a) * f a) * ((μ : ℂ) ^ (d b) * f b) := by
    intro a b
    rw [map_mul, map_pow, Complex.conj_ofReal]
    ring
  simp_rw [h_term, ← Finset.mul_sum, ← Finset.sum_mul, ← map_sum]
  rw [mul_comm, Complex.mul_conj]

theorem twoModeTubeWickHermiticity (w₁ w₂ r₁ r₂ : ℝ) :
    TubeWickHermiticity trivialStarStructure
      (momentTubeExtension (ι := Unit) (twoModeMoment w₁ w₂ r₁ r₂)) := by
  intro n α z _hz _hstar
  simp [momentTubeExtension_H, momentH, twoModeMoment, trivialStarStructure]

theorem twoModeOSReflectionPositive {w₁ w₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (r₁ r₂ : ℝ) :
    OSReflectionPositive trivialStarStructure (momentS (twoModeMoment w₁ w₂ r₁ r₂)) := by
  intro Ψ
  unfold osPreInner Finsupp.sum
  simp_rw [osKernel_trivialStarStructure_momentS, twoModeMoment_add]
  have h_split : ∀ a b : OSConfig Unit,
      star (Ψ a) * Ψ b *
        ((w₁ : ℂ) * ((r₁ : ℂ) ^ osConfigLen a * (r₁ : ℂ) ^ osConfigLen b) +
         (w₂ : ℂ) * ((r₂ : ℂ) ^ osConfigLen a * (r₂ : ℂ) ^ osConfigLen b)) =
      (w₁ : ℂ) * ((starRingEnd ℂ) (Ψ a) * Ψ b *
        ((r₁ : ℂ) ^ osConfigLen a * (r₁ : ℂ) ^ osConfigLen b)) +
      (w₂ : ℂ) * ((starRingEnd ℂ) (Ψ a) * Ψ b *
        ((r₂ : ℂ) ^ osConfigLen a * (r₂ : ℂ) ^ osConfigLen b)) := by
    intro a b
    change (starRingEnd ℂ) (Ψ a) * Ψ b * _ = _
    ring
  simp_rw [h_split, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_star_mul_pow_eq_normSq Ψ.support Ψ osConfigLen r₁,
      sum_star_mul_pow_eq_normSq Ψ.support Ψ osConfigLen r₂]
  have h_nonneg : 0 ≤ w₁ * Complex.normSq (∑ a ∈ Ψ.support, (r₁ : ℂ) ^ osConfigLen a * Ψ a) +
      w₂ * Complex.normSq (∑ a ∈ Ψ.support, (r₂ : ℂ) ^ osConfigLen a * Ψ a) :=
    add_nonneg (mul_nonneg hw₁ (Complex.normSq_nonneg _))
      (mul_nonneg hw₂ (Complex.normSq_nonneg _))
  exact_mod_cast h_nonneg

theorem twoModeOSAxioms {w₁ w₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (r₁ r₂ : ℝ) :
    OSAxioms trivialRep trivialStarStructure 1 (momentS (twoModeMoment w₁ w₂ r₁ r₂)) := by
  rw [← schwingerFromTube_momentTubeExtension]
  refine schwingerFromTube_osAxioms trivialRep trivialStarStructure
    (momentW (twoModeMoment w₁ w₂ r₁ r₂))
    (momentTubeExtension (twoModeMoment w₁ w₂ r₁ r₂))
    (momentTubeTranslationInvariant (twoModeMoment w₁ w₂ r₁ r₂))
    (momentTubeCovariant (twoModeMoment w₁ w₂ r₁ r₂))
    (twoModeTubeWickHermiticity w₁ w₂ r₁ r₂)
    (momentTubePCT (twoModeMoment w₁ w₂ r₁ r₂)) ?_
  rw [schwingerFromTube_momentTubeExtension]
  exact twoModeOSReflectionPositive hw₁ hw₂ r₁ r₂

theorem twoModePositivity {w₁ w₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (r₁ r₂ : ℝ) :
    Positivity trivialStarStructure (momentW (twoModeMoment w₁ w₂ r₁ r₂)) := by
  intro N F G hG
  let I : ℕ → ℂ := fun j => ∫ y : Fin j → Fin 4 → ℝ, F j default y
  have h_term : ∀ j k : ℕ,
      (∑ α : Fin j → Unit, ∑ α' : Fin k → Unit, ∑ β : Fin j → Unit,
        (∏ i, trivialStarStructure.C (α i) (β i)) *
          momentW (twoModeMoment w₁ w₂ r₁ r₂) (j + k) (Fin.append (β ∘ Fin.rev) α')
            (G j k α α')) =
      (starRingEnd ℂ) (I j) * I k * twoModeMoment w₁ w₂ r₁ r₂ (j + k) := by
    intro j k
    simp only [Fintype.sum_unique, trivialStarStructure, Matrix.one_apply_eq,
      Finset.prod_const_one, one_mul, momentW_apply]
    have hG_eq : (fun x : Fin (j + k) → Fin 4 → ℝ => G j k default default x) =
        fun x => (starRingEnd ℂ) (F j default (fun i => x (Fin.castAdd k (Fin.rev i)))) *
          F k default (fun i => x (Fin.natAdd j i)) := by
      ext x
      exact hG j k default default x
    rw [hG_eq, integral_split_rev_mul j k (fun y => (starRingEnd ℂ) (F j default y))
      (fun z => F k default z), integral_conj]
    dsimp [I]
    ring
  simp_rw [h_term, twoModeMoment_add]
  have h_split : ∀ j k : ℕ,
      (starRingEnd ℂ) (I j) * I k *
        ((w₁ : ℂ) * ((r₁ : ℂ) ^ j * (r₁ : ℂ) ^ k) +
         (w₂ : ℂ) * ((r₂ : ℂ) ^ j * (r₂ : ℂ) ^ k)) =
      (w₁ : ℂ) * ((starRingEnd ℂ) (I j) * I k * ((r₁ : ℂ) ^ j * (r₁ : ℂ) ^ k)) +
      (w₂ : ℂ) * ((starRingEnd ℂ) (I j) * I k * ((r₂ : ℂ) ^ j * (r₂ : ℂ) ^ k)) := by
    intro j k; ring
  simp_rw [h_split, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_star_mul_pow_eq_normSq (Finset.range (N + 1)) I (fun n => n) r₁,
      sum_star_mul_pow_eq_normSq (Finset.range (N + 1)) I (fun n => n) r₂]
  have h_nonneg : 0 ≤ w₁ * Complex.normSq (∑ a ∈ Finset.range (N + 1), (r₁ : ℂ) ^ a * I a) +
      w₂ * Complex.normSq (∑ a ∈ Finset.range (N + 1), (r₂ : ℂ) ^ a * I a) :=
    add_nonneg (mul_nonneg hw₁ (Complex.normSq_nonneg _))
      (mul_nonneg hw₂ (Complex.normSq_nonneg _))
  exact_mod_cast h_nonneg

noncomputable def twoModeOSReconstructedWightman
    {w₁ w₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (r₁ r₂ : ℝ) :
    ScalarOSReconstructedWightman 1 (momentS (twoModeMoment w₁ w₂ r₁ r₂)) where
  osAxioms := twoModeOSAxioms hw₁ hw₂ r₁ r₂
  contraction := momentOSContraction (twoModeOSAxioms hw₁ hw₂ r₁ r₂).toReflectionPositiveData rfl
  semigroup := momentHolomorphicSemigroup
    (twoModeOSAxioms hw₁ hw₂ r₁ r₂).toReflectionPositiveData rfl
    (momentOSContraction (twoModeOSAxioms hw₁ hw₂ r₁ r₂).toReflectionPositiveData rfl)
  W := momentW (twoModeMoment w₁ w₂ r₁ r₂)
  E := momentTubeExtension (twoModeMoment w₁ w₂ r₁ r₂)
  schwinger_eq _ _ _ _ := rfl
  tube_covariant := momentTubeCovariant (twoModeMoment w₁ w₂ r₁ r₂)
  tube_pct := momentTubePCT (twoModeMoment w₁ w₂ r₁ r₂)
  spectrum := momentZeroMomentumSpectrumCondition (twoModeMoment w₁ w₂ r₁ r₂)
  poincare := momentPoincareCovariant (twoModeMoment w₁ w₂ r₁ r₂)
  weakLocality := momentWeakLocality (twoModeMoment w₁ w₂ r₁ r₂)
  positivity := twoModePositivity hw₁ hw₂ r₁ r₂

def coherentCoeff (r : ℝ) : ℕ → ℂ :=
  twoModeMoment 1 0 r 0

@[simp]
lemma coherentCoeff_apply (r : ℝ) (n : ℕ) :
    coherentCoeff r n = (r : ℂ) ^ n := by
  dsimp [coherentCoeff, twoModeMoment]
  push_cast
  ring

def coherentS (r : ℝ) : SchwingerFamily Unit :=
  momentS (coherentCoeff r)

noncomputable def coherentW (r : ℝ) : WightmanFamily Unit :=
  momentW (coherentCoeff r)

noncomputable def coherentOSReconstructedWightman (r : ℝ) :
    ScalarOSReconstructedWightman 1 (coherentS r) :=
  twoModeOSReconstructedWightman zero_le_one le_rfl r 0

theorem coherentOSTimeCluster (r : ℝ) :
    OSTimeClusterDecomposition (coherentOSReconstructedWightman r).osData := by
  intro A B
  have h_const : (fun τ : ℝ =>
      osKernel trivialStarStructure (coherentOSReconstructedWightman r).osData.𝒮 A
        (osConfigTimeShift (max τ 0) (le_max_right τ 0) B)) =
      fun _ : ℝ =>
        osKernel trivialStarStructure (coherentOSReconstructedWightman r).osData.𝒮 A
          (osVacuumConfig Unit) *
        osKernel trivialStarStructure (coherentOSReconstructedWightman r).osData.𝒮
          (osVacuumConfig Unit) B := by
    ext τ
    change osKernel trivialStarStructure (momentS (coherentCoeff r)) A
        (osConfigTimeShift (max τ 0) (le_max_right τ 0) B) =
      osKernel trivialStarStructure (momentS (coherentCoeff r)) A (osVacuumConfig Unit) *
        osKernel trivialStarStructure (momentS (coherentCoeff r)) (osVacuumConfig Unit) B
    rw [osKernel_trivialStarStructure_momentS, osKernel_trivialStarStructure_momentS,
        osKernel_trivialStarStructure_momentS]
    change coherentCoeff r (A.1 + B.1) = coherentCoeff r (A.1 + 0) * coherentCoeff r (0 + B.1)
    simp [coherentCoeff_apply, pow_add]
  rw [h_const]
  exact tendsto_const_nhds

theorem coherentOSSpatialCluster (r : ℝ) :
    OSSpatialClusterDecomposition (coherentOSReconstructedWightman r).osData := by
  intro a _ha A B
  have h_const : (fun t : ℝ =>
      osKernel trivialStarStructure (coherentOSReconstructedWightman r).osData.𝒮 A
        (osConfigSpatialShift (t • a) B)) =
      fun _ : ℝ =>
        osKernel trivialStarStructure (coherentOSReconstructedWightman r).osData.𝒮 A
          (osVacuumConfig Unit) *
        osKernel trivialStarStructure (coherentOSReconstructedWightman r).osData.𝒮
          (osVacuumConfig Unit) B := by
    ext t
    change osKernel trivialStarStructure (momentS (coherentCoeff r)) A
        (osConfigSpatialShift (t • a) B) =
      osKernel trivialStarStructure (momentS (coherentCoeff r)) A (osVacuumConfig Unit) *
        osKernel trivialStarStructure (momentS (coherentCoeff r)) (osVacuumConfig Unit) B
    rw [osKernel_trivialStarStructure_momentS, osKernel_trivialStarStructure_momentS,
        osKernel_trivialStarStructure_momentS]
    change coherentCoeff r (A.1 + B.1) = coherentCoeff r (A.1 + 0) * coherentCoeff r (0 + B.1)
    simp [coherentCoeff_apply, pow_add]
  rw [h_const]
  exact tendsto_const_nhds

noncomputable def z2FreeCoeff : ℕ → ℂ :=
  twoModeMoment (1 / 2) (1 / 2) 1 (-1)

noncomputable def z2FreeS : SchwingerFamily Unit :=
  momentS z2FreeCoeff

noncomputable def z2FreeW : WightmanFamily Unit :=
  momentW z2FreeCoeff

noncomputable def z2FreeTubeExtension : TubeExtension z2FreeW :=
  momentTubeExtension z2FreeCoeff

noncomputable def z2FreeOSReconstructedWightman :
    ScalarOSReconstructedWightman 1 z2FreeS :=
  twoModeOSReconstructedWightman (by positivity) (by positivity) 1 (-1)

noncomputable def z2FreeOSData : OSReflectionPositiveData trivialRep trivialStarStructure :=
  z2FreeOSReconstructedWightman.osData

lemma z2FreeCoeff_eq_ite (n : ℕ) :
    z2FreeCoeff n = if n % 2 = 0 then 1 else 0 := by
  dsimp [z2FreeCoeff, twoModeMoment]
  rw [one_pow]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have hmod : (2 * k) % 2 = 0 := by omega
    rw [if_pos hmod, pow_mul, neg_one_sq, one_pow]
    push_cast
    ring
  · have hmod : (2 * k + 1) % 2 ≠ 0 := by omega
    rw [if_neg hmod, pow_add, pow_mul, neg_one_sq, one_pow, pow_one]
    push_cast
    ring

@[simp] theorem z2FreeCoeff_zero : z2FreeCoeff 0 = 1 := by rw [z2FreeCoeff_eq_ite]; rfl
@[simp] theorem z2FreeCoeff_one : z2FreeCoeff 1 = 0 := by rw [z2FreeCoeff_eq_ite]; rfl
@[simp] theorem z2FreeCoeff_two : z2FreeCoeff 2 = 1 := by rw [z2FreeCoeff_eq_ite]; rfl
@[simp] theorem z2FreeCoeff_three : z2FreeCoeff 3 = 0 := by rw [z2FreeCoeff_eq_ite]; rfl
@[simp] theorem z2FreeCoeff_four : z2FreeCoeff 4 = 1 := by rw [z2FreeCoeff_eq_ite]; rfl

theorem z2FreeS_vacuumNormalized : OSVacuumNormalized z2FreeS := by
  unfold OSVacuumNormalized z2FreeS momentS
  exact z2FreeCoeff_zero

@[simp]
theorem z2FreeS_one_eq_zero (α : Fin 1 → Unit) (x : Fin 1 → Fin 4 → ℝ) :
    z2FreeS 1 α x = 0 := z2FreeCoeff_one

@[simp]
theorem z2FreeS_two_eq_one (α : Fin 2 → Unit) (x : Fin 2 → Fin 4 → ℝ) :
    z2FreeS 2 α x = 1 := z2FreeCoeff_two

@[simp]
theorem z2FreeW_one_eq_zero (α : Fin 1 → Unit) (f : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    z2FreeW 1 α f = 0 := by
  change z2FreeCoeff 1 * ∫ x, f x = 0
  rw [z2FreeCoeff_one, zero_mul]

@[simp]
theorem z2FreeW_two_unitIntegralSchwartz (α : Fin 2 → Unit) :
    z2FreeW 2 α (unitIntegralSchwartz 2) = 1 := by
  change momentW z2FreeCoeff 2 α (unitIntegralSchwartz 2) = 1
  rw [momentW_unitIntegralSchwartz, z2FreeCoeff_two]

theorem z2FreeW_twoPoint_nondegenerate :
    ∃ (α : Fin 2 → Unit) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), z2FreeW 2 α f ≠ 0 :=
  ⟨default, unitIntegralSchwartz 2, by rw [z2FreeW_two_unitIntegralSchwartz]; exact one_ne_zero⟩

theorem z2FreeW_ne_vacW : z2FreeW ≠ vacW := by
  intro h
  have h2 : z2FreeW 2 (default : Fin 2 → Unit) (unitIntegralSchwartz 2) =
      vacW 2 (default : Fin 2 → Unit) (unitIntegralSchwartz 2) := by rw [h]
  rw [z2FreeW_two_unitIntegralSchwartz, vacW_succ_apply] at h2
  exact one_ne_zero h2

theorem z2FreeS_ne_vacS : z2FreeS ≠ vacS := by
  intro h
  have h2 : z2FreeS 2 (default : Fin 2 → Unit) (euclidOrderedBasePoint 2) =
      vacS 2 (default : Fin 2 → Unit) (euclidOrderedBasePoint 2) := by rw [h]
  rw [z2FreeS_two_eq_one, vacS_succ] at h2
  exact one_ne_zero h2

theorem z2Free_spin_statistics_unconditional {η : ℂ} {𝒮 : SchwingerFamily Unit}
    (P : ScalarOSReconstructedWightman η 𝒮) (hW : P.W = z2FreeW) :
    η = 1 := by
  refine scalar_os_spin_statistics_unconditional P ?_
  rw [hW]
  exact z2FreeW_twoPoint_nondegenerate

theorem coherent_spin_statistics_unconditional {η : ℂ} {r : ℝ} (hr : r ≠ 0)
    {𝒮 : SchwingerFamily Unit} (P : ScalarOSReconstructedWightman η 𝒮)
    (hW : P.W = coherentW r) :
    η = 1 := by
  refine scalar_os_spin_statistics_unconditional P ?_
  rw [hW]
  refine ⟨default, unitIntegralSchwartz 2, ?_⟩
  change momentW (coherentCoeff r) 2 default (unitIntegralSchwartz 2) ≠ 0
  rw [momentW_unitIntegralSchwartz, coherentCoeff_apply]
  exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hr)

noncomputable def osBaseConfig (n : ℕ) : OSConfig Unit :=
  ⟨n, (default, ⟨euclidOrderedBasePoint n, euclidOrderedBasePoint_mem_posOrderedEuclidN n⟩)⟩

noncomputable def z2FreeOneParticle : OSHilbert z2FreeOSData :=
  osBasis z2FreeOSData (osBaseConfig 1)

theorem osBasis_z2FreeOSData_eq_of_mod_two_eq (A B : OSConfig Unit)
    (h : A.1 % 2 = B.1 % 2) :
    osBasis z2FreeOSData A = osBasis z2FreeOSData B := by
  have h_sub : ‖osBasisPre z2FreeOSData A - osBasisPre z2FreeOSData B‖ = 0 := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ)]
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    simp only [inner_osBasisPre]
    change Real.sqrt (RCLike.re
      (osKernel trivialStarStructure z2FreeS A A -
       osKernel trivialStarStructure z2FreeS A B -
       (osKernel trivialStarStructure z2FreeS B A -
        osKernel trivialStarStructure z2FreeS B B))) = 0
    simp only [z2FreeS, osKernel_trivialStarStructure_momentS, osConfigLen, z2FreeCoeff_eq_ite]
    have hAA : (A.1 + A.1) % 2 = 0 := by omega
    have hAB : (A.1 + B.1) % 2 = 0 := by omega
    have hBA : (B.1 + A.1) % 2 = 0 := by omega
    have hBB : (B.1 + B.1) % 2 = 0 := by omega
    rw [if_pos hAA, if_pos hAB, if_pos hBA, if_pos hBB]
    simp
  rw [← sub_eq_zero, ← norm_eq_zero]
  change ‖toOSHilbert z2FreeOSData (osBasisPre z2FreeOSData A) -
    toOSHilbert z2FreeOSData (osBasisPre z2FreeOSData B)‖ = 0
  rw [← map_sub, norm_toOSHilbert]
  exact h_sub

theorem osBasis_z2FreeOSData_eq_ite (A : OSConfig Unit) :
    osBasis z2FreeOSData A =
      if A.1 % 2 = 0 then osVacuum z2FreeOSData else z2FreeOneParticle := by
  by_cases h : A.1 % 2 = 0
  · rw [if_pos h]
    exact osBasis_z2FreeOSData_eq_of_mod_two_eq A (osVacuumConfig Unit) h
  · rw [if_neg h]
    have h1 : A.1 % 2 = (osBaseConfig 1).1 % 2 := by
      change A.1 % 2 = 1 % 2
      omega
    exact osBasis_z2FreeOSData_eq_of_mod_two_eq A (osBaseConfig 1) h1

@[simp]
theorem inner_osVacuum_z2FreeOSData_self :
    ⟪osVacuum z2FreeOSData, osVacuum z2FreeOSData⟫_ℂ = 1 := by
  rw [inner_osVacuum_self]
  exact z2FreeCoeff_zero

@[simp]
theorem norm_osVacuum_z2FreeOSData :
    ‖osVacuum z2FreeOSData‖ = 1 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_osVacuum_z2FreeOSData_self]
  simp

@[simp]
theorem inner_osVacuum_z2FreeOneParticle :
    ⟪osVacuum z2FreeOSData, z2FreeOneParticle⟫_ℂ = 0 := by
  dsimp [z2FreeOneParticle]
  rw [inner_osVacuum_osBasis]
  exact z2FreeCoeff_one

@[simp]
theorem inner_z2FreeOneParticle_osVacuum :
    ⟪z2FreeOneParticle, osVacuum z2FreeOSData⟫_ℂ = 0 := by
  rw [← inner_conj_symm, inner_osVacuum_z2FreeOneParticle, map_zero]

@[simp]
theorem inner_z2FreeOneParticle_self :
    ⟪z2FreeOneParticle, z2FreeOneParticle⟫_ℂ = 1 := by
  dsimp [z2FreeOneParticle]
  rw [inner_osBasis]
  change osKernel trivialStarStructure z2FreeS (osBaseConfig 1) (osBaseConfig 1) = 1
  rw [z2FreeS, osKernel_trivialStarStructure_momentS]
  exact z2FreeCoeff_two

@[simp]
theorem norm_z2FreeOneParticle : ‖z2FreeOneParticle‖ = 1 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_z2FreeOneParticle_self]
  simp

theorem z2FreeOneParticle_ne_zero : z2FreeOneParticle ≠ 0 := by
  intro h
  have := norm_z2FreeOneParticle
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem z2FreeHilbert_eq_vacuum_add_oneParticle (Φ : OSHilbert z2FreeOSData) :
    Φ = ⟪osVacuum z2FreeOSData, Φ⟫_ℂ • osVacuum z2FreeOSData +
        ⟪z2FreeOneParticle, Φ⟫_ℂ • z2FreeOneParticle := by
  have h_basis : ∀ A : OSConfig Unit,
      osBasis z2FreeOSData A =
        ⟪osVacuum z2FreeOSData, osBasis z2FreeOSData A⟫_ℂ • osVacuum z2FreeOSData +
        ⟪z2FreeOneParticle, osBasis z2FreeOSData A⟫_ℂ • z2FreeOneParticle := by
    intro A
    rw [osBasis_z2FreeOSData_eq_ite A]
    split_ifs with h
    · rw [inner_osVacuum_z2FreeOSData_self, inner_z2FreeOneParticle_osVacuum,
        one_smul, zero_smul, add_zero]
    · rw [inner_osVacuum_z2FreeOneParticle, inner_z2FreeOneParticle_self,
        zero_smul, one_smul, zero_add]
  induction Φ using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change toOSHilbert z2FreeOSData Ψ =
      ⟪osVacuum z2FreeOSData, toOSHilbert z2FreeOSData Ψ⟫_ℂ • osVacuum z2FreeOSData +
      ⟪z2FreeOneParticle, toOSHilbert z2FreeOSData Ψ⟫_ℂ • z2FreeOneParticle
    have h_expand : toOSHilbert z2FreeOSData Ψ =
        ∑ A ∈ Ψ.toFinsupp.support, Ψ.toFinsupp A • osBasis z2FreeOSData A := by
      conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre z2FreeOSData Ψ]
      rw [map_finsuppSum]
      unfold Finsupp.sum
      refine Finset.sum_congr rfl (fun A _ => (toOSHilbert z2FreeOSData).map_smul _ _)
    rw [h_expand, inner_sum, inner_sum, Finset.sum_smul, Finset.sum_smul,
        ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    rw [inner_smul_right, inner_smul_right, mul_smul, mul_smul, ← smul_add, ← h_basis A]

noncomputable def orthogonalTwoLinearIsometryEquiv
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e₀ e₁ : H)
    (h00 : ⟪e₀, e₀⟫_ℂ = 1) (h01 : ⟪e₀, e₁⟫_ℂ = 0)
    (h10 : ⟪e₁, e₀⟫_ℂ = 0) (h11 : ⟪e₁, e₁⟫_ℂ = 1)
    (hn0 : ‖e₀‖ = 1) (hn1 : ‖e₁‖ = 1)
    (h_span : ∀ Φ : H, Φ = ⟪e₀, Φ⟫_ℂ • e₀ + ⟪e₁, Φ⟫_ℂ • e₁) :
    H ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun Φ := WithLp.toLp 2 ![⟪e₀, Φ⟫_ℂ, ⟪e₁, Φ⟫_ℂ]
  map_add' x y := by
    ext i
    fin_cases i <;> simp
  map_smul' c x := by
    ext i
    fin_cases i <;> simp
  invFun v := v.ofLp 0 • e₀ + v.ofLp 1 • e₁
  left_inv Φ := (h_span Φ).symm
  right_inv v := by
    ext i
    fin_cases i
    · simp [h01, hn0]
    · simp [h10, hn1]
  norm_map' Φ := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    change Real.sqrt (‖⟪e₀, Φ⟫_ℂ‖ ^ 2 + ‖⟪e₁, Φ⟫_ℂ‖ ^ 2) = ‖Φ‖
    conv_rhs => rw [h_span Φ, norm_eq_sqrt_re_inner (𝕜 := ℂ)]
    congr 1
    rw [inner_add_left, inner_add_right, inner_add_right,
        inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
        inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
        h00, h01, h10, h11]
    have h_re : ∀ z : ℂ, RCLike.re (starRingEnd ℂ z * (z * 1)) = ‖z‖ ^ 2 := by
      intro z
      rw [mul_one, mul_comm, Complex.mul_conj]
      exact Complex.normSq_eq_norm_sq z
    simp only [mul_zero, add_zero, zero_add, map_add, h_re]

noncomputable def z2FreeHilbertLinearIsometryEquiv :
    OSHilbert z2FreeOSData ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  orthogonalTwoLinearIsometryEquiv
    (osVacuum z2FreeOSData) z2FreeOneParticle
    inner_osVacuum_z2FreeOSData_self inner_osVacuum_z2FreeOneParticle
    inner_z2FreeOneParticle_osVacuum inner_z2FreeOneParticle_self
    norm_osVacuum_z2FreeOSData norm_z2FreeOneParticle
    z2FreeHilbert_eq_vacuum_add_oneParticle

theorem norm_schwinger_twoPoint_le_sqrt_osKernel_fourPoint
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S)
    (α : Fin 2 → ι) (y : posOrderedEuclidN 2) :
    ‖D.𝒮 2 α y.val‖ ≤
      ‖osVacuumPre D‖ *
        Real.sqrt (RCLike.re (osKernel S D.𝒮 ⟨2, (α, y)⟩ ⟨2, (α, y)⟩)) := by
  let A₂ : OSConfig ι := ⟨2, (α, y)⟩
  have h_eq : D.𝒮 2 α y.val = ⟪osVacuumPre D, osBasisPre D A₂⟫_ℂ :=
    (inner_osVacuumPre_osBasisPre D A₂).symm
  rw [h_eq]
  have h_cs := osPreHilbert_cauchy_schwarz D (osVacuumPre D) (osBasisPre D A₂)
  have h_norm : ‖osBasisPre D A₂‖ =
      Real.sqrt (RCLike.re (osKernel S D.𝒮 A₂ A₂)) := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_osBasisPre]
  rwa [h_norm] at h_cs

theorem schwinger_twoPoint_posOrdered_eq_zero_of_fourPoint_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S)
    (h4 : ∀ (γ : Fin 4 → ι) (z : Fin 4 → Fin 4 → ℝ),
      z ∈ orderedEuclidN 4 → D.𝒮 4 γ z = 0)
    (α : Fin 2 → ι) {y : Fin 2 → Fin 4 → ℝ} (hy : y ∈ posOrderedEuclidN 2) :
    D.𝒮 2 α y = 0 := by
  let A₂ : OSConfig ι := ⟨2, (α, ⟨y, hy⟩)⟩
  have hK : osKernel S D.𝒮 A₂ A₂ = 0 :=
    osKernel_eq_zero_of_schwinger_eq_zero S D.𝒮 A₂ A₂ h4
  have h_orth : ⟪osBasisPre D A₂, osVacuumPre D⟫_ℂ = 0 :=
    inner_osBasisPre_eq_zero_of_osKernel_self_eq_zero D hK (osVacuumPre D)
  rw [inner_osBasisPre_osVacuumPre] at h_orth
  exact star_eq_zero.mp h_orth

theorem schwinger_twoPoint_eq_zero_of_fourPoint_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (h4 : ∀ (γ : Fin 4 → ι) (z : Fin 4 → Fin 4 → ℝ),
      z ∈ orderedEuclidN 4 → D.𝒮 4 γ z = 0)
    (α : Fin 2 → ι) {x : Fin 2 → Fin 4 → ℝ} (hx : x ∈ orderedEuclidN 2) :
    D.𝒮 2 α x = 0 :=
  schwinger_eq_zero_of_posOrderedEuclidN_eq_zero htrans 2 α
    (fun _y hy => schwinger_twoPoint_posOrdered_eq_zero_of_fourPoint_eq_zero D h4 α hy) hx

theorem exists_fourPoint_ne_zero_of_twoPoint_ne_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (h2 : ∃ (α : Fin 2 → ι) (x : Fin 2 → Fin 4 → ℝ),
      x ∈ orderedEuclidN 2 ∧ D.𝒮 2 α x ≠ 0) :
    ∃ (γ : Fin 4 → ι) (z : Fin 4 → Fin 4 → ℝ),
      z ∈ orderedEuclidN 4 ∧ D.𝒮 4 γ z ≠ 0 := by
  by_contra h4
  push Not at h4
  rcases h2 with ⟨α, x, hx, hne⟩
  exact hne (schwinger_twoPoint_eq_zero_of_fourPoint_eq_zero D htrans h4 α hx)

theorem schwinger_all_nPoint_eq_zero_iff_fourPoint_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮) :
    (∀ (n : ℕ), 1 ≤ n → ∀ (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = 0) ↔
    (∀ (γ : Fin 4 → ι) (z : Fin 4 → Fin 4 → ℝ),
      z ∈ orderedEuclidN 4 → D.𝒮 4 γ z = 0) := by
  refine ⟨fun hall γ z hz => hall 4 (by omega) γ z hz, fun h4 n hn α x hx => ?_⟩
  exact schwinger_eq_zero_of_twoPoint_eq_zero D htrans
    (fun β _y hy => schwinger_twoPoint_eq_zero_of_fourPoint_eq_zero D htrans h4 β hy)
    n hn α hx

noncomputable def vacSpectralDecomposition
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    OSSpectralDecomposition (vacOSData R S) (vacOSContraction R S) 1 where
  E _ := 0
  energy_nonneg _ := le_rfl
  P _ := rankOneProjCLM (osVacuum (vacOSData R S))
  proj_selfAdjoint _ x y := rankOneProjCLM_selfAdjoint _ x y
  proj_mul j k := by
    fin_cases j
    fin_cases k
    rw [if_pos rfl]
    exact rankOneProjCLM_comp_self
      (inner_osVacuum_self_of_normalized (vacOSData R S) vacS_vacuumNormalized)
  sum_proj x := by
    rw [Fin.sum_univ_one, rankOneProjCLM_apply]
    exact (vacHilbert_eq_smul_osVacuum R S x).symm
  semigroup_eq τ hτ x := by
    rw [vacOSContractionSemigroup_eq_id R S (vacOSContraction R S) τ hτ,
        ContinuousLinearMap.id_apply, Fin.sum_univ_one, laplaceExp_zero_left,
        one_smul, rankOneProjCLM_apply]
    exact vacHilbert_eq_smul_osVacuum R S x
  vacuum_eq z := by
    rw [Fin.sum_univ_one, laplaceExp_zero_left, one_smul, rankOneProjCLM_apply,
        inner_osVacuum_self_of_normalized (vacOSData R S) vacS_vacuumNormalized, one_smul]
  comm_spatial htrans a _ := by
    rw [vacOSSpatialTranslate_eq_id R S htrans a, ContinuousLinearMap.id_comp,
        ContinuousLinearMap.comp_id]

noncomputable def vacSpectralHolomorphicSemigroup
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    OSHolomorphicSemigroup (vacOSData R S) (vacOSContraction R S) :=
  (vacSpectralDecomposition R S).toOSHolomorphicSemigroup

noncomputable def vacEuclideanTubeBridge
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) :
    OSEuclideanTubeBridge R S η vacS :=
  osEuclideanTubeBridgeOfTubeExtension R S η vacS vacW vacTubeExtension
    (fun n α x _ => by rw [schwingerFromTube_vacTubeExtension])
    (vacTubeCovariant R) (vacTubePCT R η)
    vacZeroMomentumSpectrumCondition (vacPoincareCovariant R) (vacWeakLocality η) (vacPositivity S)

noncomputable def vacReconstructedWightmanOfTimeCluster
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) :
    OSReconstructedWightman R S η vacS :=
  osReconstructedWightmanOfTimeCluster R S η vacS
    (vacOSAxioms R S η) (vacOSTimeCluster R S)
    (vacSpectralHolomorphicSemigroup R S)
    (vacEuclideanTubeBridge R S η)

@[simp]
theorem momentOSSpatialTranslate_eq_id {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {c : ℕ → ℂ} (D : OSReflectionPositiveData R S) (hD : D.𝒮 = momentS c)
    (htrans : OSTranslationInvariant D.𝒮) (a : Fin 3 → ℝ) :
    osSpatialTranslate D htrans a = ContinuousLinearMap.id ℂ (OSHilbert D) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change osSpatialTranslate D htrans a (toOSHilbert D Ψ) = toOSHilbert D Ψ
    rw [osSpatialTranslate_toOSHilbert]
    conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D Ψ]
    conv_rhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D Ψ]
    rw [map_finsuppSum, map_finsuppSum, map_finsuppSum]
    refine Finsupp.sum_congr (fun A _ => ?_)
    rw [LinearMap.map_smul, (toOSHilbert D).map_smul, (toOSHilbert D).map_smul]
    congr 1
    unfold osSpatialTranslateLM
    rw [osLiftConfigMap_osBasisPre]
    exact osBasis_eq_of_momentS D hD (osConfigSpatialShift a A) A rfl HEq.rfl

theorem z2FreeOSContraction : OSContractionCondition z2FreeOSData :=
  momentOSContraction z2FreeOSData rfl

@[simp]
theorem z2FreeOSContractionSemigroup_eq_id (τ : ℝ) (hτ : 0 ≤ τ) :
    osContractionSemigroup z2FreeOSData z2FreeOSContraction τ hτ =
      ContinuousLinearMap.id ℂ (OSHilbert z2FreeOSData) :=
  momentOSContractionSemigroup_eq_id z2FreeOSData rfl z2FreeOSContraction τ hτ

@[simp]
theorem z2FreeOSSpatialTranslate_eq_id (htrans : OSTranslationInvariant z2FreeOSData.𝒮)
    (a : Fin 3 → ℝ) :
    osSpatialTranslate z2FreeOSData htrans a =
      ContinuousLinearMap.id ℂ (OSHilbert z2FreeOSData) :=
  momentOSSpatialTranslate_eq_id z2FreeOSData rfl htrans a

noncomputable def z2FreeSpectralDecomposition :
    OSSpectralDecomposition z2FreeOSData z2FreeOSContraction 2 where
  E _ := 0
  energy_nonneg _ := le_rfl
  P i :=
    if i = 0 then
      rankOneProjCLM (osVacuum z2FreeOSData)
    else
      rankOneProjCLM z2FreeOneParticle
  proj_selfAdjoint i x y := by
    fin_cases i <;> exact rankOneProjCLM_selfAdjoint _ x y
  proj_mul j k := by
    fin_cases j <;> fin_cases k
    · simp only [Fin.isValue, ↓reduceIte]
      exact rankOneProjCLM_comp_self inner_osVacuum_z2FreeOSData_self
    · simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, zero_ne_one, ↓reduceIte, one_ne_zero]
      exact rankOneProjCLM_comp_eq_zero_of_orth inner_osVacuum_z2FreeOneParticle
    · simp only [Fin.isValue, Fin.mk_one, one_ne_zero, ↓reduceIte, Fin.zero_eta]
      exact rankOneProjCLM_comp_eq_zero_of_orth inner_z2FreeOneParticle_osVacuum
    · simp only [Fin.isValue, Fin.mk_one, one_ne_zero, ↓reduceIte]
      exact rankOneProjCLM_comp_self inner_z2FreeOneParticle_self
  sum_proj x := by
    rw [Fin.sum_univ_two]
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    rw [if_pos rfl, if_neg h10, rankOneProjCLM_apply, rankOneProjCLM_apply]
    exact (z2FreeHilbert_eq_vacuum_add_oneParticle x).symm
  semigroup_eq τ hτ x := by
    rw [z2FreeOSContractionSemigroup_eq_id τ hτ, ContinuousLinearMap.id_apply,
        Fin.sum_univ_two]
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    rw [laplaceExp_zero_left, one_smul, one_smul, if_pos rfl, if_neg h10,
        rankOneProjCLM_apply, rankOneProjCLM_apply]
    exact z2FreeHilbert_eq_vacuum_add_oneParticle x
  vacuum_eq z := by
    rw [Fin.sum_univ_two]
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    rw [laplaceExp_zero_left, one_smul, one_smul, if_pos rfl, if_neg h10,
        rankOneProjCLM_apply, rankOneProjCLM_apply,
        inner_osVacuum_z2FreeOSData_self, inner_z2FreeOneParticle_osVacuum,
        one_smul, zero_smul, add_zero]
  comm_spatial htrans a i := by
    rw [z2FreeOSSpatialTranslate_eq_id htrans a, ContinuousLinearMap.id_comp,
        ContinuousLinearMap.comp_id]

noncomputable def z2FreeSpectralHolomorphicSemigroup :
    OSHolomorphicSemigroup z2FreeOSData z2FreeOSContraction :=
  z2FreeSpectralDecomposition.toOSHolomorphicSemigroup

noncomputable def twoModeEuclideanTubeBridge
    {w₁ w₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (r₁ r₂ : ℝ) :
    OSEuclideanTubeBridge trivialRep trivialStarStructure 1
      (momentS (twoModeMoment w₁ w₂ r₁ r₂)) :=
  osEuclideanTubeBridgeOfTubeExtension trivialRep trivialStarStructure 1
    (momentS (twoModeMoment w₁ w₂ r₁ r₂))
    (momentW (twoModeMoment w₁ w₂ r₁ r₂))
    (momentTubeExtension (twoModeMoment w₁ w₂ r₁ r₂))
    (fun _ _ _ _ => rfl)
    (momentTubeCovariant (twoModeMoment w₁ w₂ r₁ r₂))
    (momentTubePCT (twoModeMoment w₁ w₂ r₁ r₂))
    (momentZeroMomentumSpectrumCondition (twoModeMoment w₁ w₂ r₁ r₂))
    (momentPoincareCovariant (twoModeMoment w₁ w₂ r₁ r₂))
    (momentWeakLocality (twoModeMoment w₁ w₂ r₁ r₂))
    (twoModePositivity hw₁ hw₂ r₁ r₂)

noncomputable def z2FreeEuclideanTubeBridge :
    OSEuclideanTubeBridge trivialRep trivialStarStructure 1 z2FreeS :=
  twoModeEuclideanTubeBridge (by positivity) (by positivity) 1 (-1)

theorem z2FreeOSDiagonalKernelBounded :
    OSDiagonalKernelBounded trivialStarStructure z2FreeS := by
  intro A
  refine ⟨1, fun τ hτ => ?_⟩
  change ‖osKernel trivialStarStructure (momentS z2FreeCoeff)
    (osConfigTimeShift τ hτ A) (osConfigTimeShift τ hτ A)‖ ≤ 1
  rw [osKernel_trivialStarStructure_momentS, osConfigLen, z2FreeCoeff_eq_ite]
  have h_even : ((osConfigTimeShift τ hτ A).1 + (osConfigTimeShift τ hτ A).1) % 2 = 0 := by omega
  rw [if_pos h_even]
  simp

noncomputable def z2FreeReconstructedWightmanOfDiagonalBounded :
    ScalarOSReconstructedWightman 1 z2FreeS :=
  osReconstructedWightmanOfDiagonalBounded trivialRep trivialStarStructure 1 z2FreeS
    z2FreeOSReconstructedWightman.osAxioms
    z2FreeOSDiagonalKernelBounded
    z2FreeSpectralHolomorphicSemigroup
    z2FreeEuclideanTubeBridge

noncomputable def discreteKallenLehmannTube
    (N : ℕ) (w E : Fin N → ℝ) (z : Fin 2 → Fin 4 → ℂ) : ℂ :=
  ∑ a : Fin N, (w a : ℂ) * spectralTwoPointTube (E a) z

noncomputable def discreteKallenLehmannEuclid
    (N : ℕ) (w E : Fin N → ℝ) (x : Fin 2 → Fin 4 → ℝ) : ℂ :=
  ∑ a : Fin N, (w a : ℂ) * euclidSpectralTwoPoint (E a) x

@[simp]
theorem discreteKallenLehmannTube_wickEmbedN
    (N : ℕ) (w E : Fin N → ℝ) (x : Fin 2 → Fin 4 → ℝ) :
    discreteKallenLehmannTube N w E (wickEmbedN 2 x) =
      discreteKallenLehmannEuclid N w E x := by
  unfold discreteKallenLehmannTube discreteKallenLehmannEuclid
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [spectralTwoPointTube_wickEmbedN_eq_euclidSpectralTwoPoint]

theorem differentiable_discreteKallenLehmannTube (N : ℕ) (w E : Fin N → ℝ) :
    Differentiable ℂ (discreteKallenLehmannTube N w E) := by
  unfold discreteKallenLehmannTube
  have h_term : ∀ a : Fin N,
      Differentiable ℂ (fun z => (w a : ℂ) * spectralTwoPointTube (E a) z) :=
    fun a => (differentiable_const (w a : ℂ)).mul (differentiable_spectralTwoPointTube (E a))
  fun_prop

theorem analyticOn_discreteKallenLehmannTube
    (N : ℕ) (w E : Fin N → ℝ) (s : Set (Fin 2 → Fin 4 → ℂ)) :
    AnalyticOn ℂ (discreteKallenLehmannTube N w E) s :=
  AnalyticOnNhd.analyticOn (fun z _ => by
    unfold discreteKallenLehmannTube
    refine analyticAt_finset_sum_normed Finset.univ (fun a _ => ?_)
    exact analyticAt_const.mul (analyticAt_spectralTwoPointTube (E a) z))

@[simp]
theorem discreteKallenLehmannTube_add_const
    (N : ℕ) (w E : Fin N → ℝ) (z : Fin 2 → Fin 4 → ℂ) (a : Fin 4 → ℂ) :
    discreteKallenLehmannTube N w E (fun k => z k + a) =
      discreteKallenLehmannTube N w E z := by
  unfold discreteKallenLehmannTube
  refine Finset.sum_congr rfl (fun idx _ => ?_)
  rw [spectralTwoPointTube_add_const]

theorem discreteKallenLehmannEuclid_sesquilinear_eq
    (N : ℕ) (w E : Fin N → ℝ) (m : ℕ) (c : Fin m → ℂ) (x : Fin m → Fin 1 → Fin 4 → ℝ) :
    (∑ j : Fin m, ∑ k : Fin m,
      star (c j) * c k *
        discreteKallenLehmannEuclid N w E (osConcatPoint 1 1 (x j) (x k))) =
      ∑ a : Fin N, (w a : ℂ) *
        (‖∑ k : Fin m, c k * laplaceExp (E a) (x k 0 0 : ℂ)‖ ^ 2 : ℂ) := by
  unfold discreteKallenLehmannEuclid
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_comm]
  have h_pull : ∀ j k : Fin m,
      star (c j) * c k * ((w a : ℂ) *
        euclidSpectralTwoPoint (E a) (osConcatPoint 1 1 (x j) (x k))) =
      (w a : ℂ) * (star (c j) * c k *
        euclidSpectralTwoPoint (E a) (osConcatPoint 1 1 (x j) (x k))) := by
    intro j k
    ring
  simp_rw [h_pull, ← Finset.mul_sum]
  rw [euclidSpectralTwoPoint_sesquilinear_eq_norm_sq]

theorem discreteKallenLehmannEuclid_reflectionPositive
    {N : ℕ} {w : Fin N → ℝ} (hw : ∀ a : Fin N, 0 ≤ w a) (E : Fin N → ℝ)
    (m : ℕ) (c : Fin m → ℂ) (x : Fin m → Fin 1 → Fin 4 → ℝ) :
    0 ≤ RCLike.re (∑ j : Fin m, ∑ k : Fin m,
      star (c j) * c k *
        discreteKallenLehmannEuclid N w E (osConcatPoint 1 1 (x j) (x k))) := by
  rw [discreteKallenLehmannEuclid_sesquilinear_eq, map_sum]
  refine Finset.sum_nonneg (fun a _ => ?_)
  have h_re :
      RCLike.re ((w a : ℂ) *
        (‖∑ k : Fin m, c k * laplaceExp (E a) (x k 0 0 : ℂ)‖ ^ 2 : ℂ)) =
        w a * ‖∑ k : Fin m, c k * laplaceExp (E a) (x k 0 0 : ℂ)‖ ^ 2 := by
    change ((w a : ℂ) *
      ((‖∑ k : Fin m, c k * laplaceExp (E a) (x k 0 0 : ℂ)‖ : ℂ) ^ 2)).re = _
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [h_re]
  exact mul_nonneg (hw a) (sq_nonneg _)

theorem tendsto_discreteKallenLehmannEuclid_timeShift_atTop_zero
    {N : ℕ} (w : Fin N → ℝ) {E : Fin N → ℝ} (hE : ∀ a : Fin N, 0 < E a)
    (x y : Fin 1 → Fin 4 → ℝ) :
    Tendsto
      (fun τ : ℝ =>
        discreteKallenLehmannEuclid N w E
          (osConcatPoint 1 1 x (fun i => y i + euclidTimeVec τ)))
      atTop (𝓝 0) := by
  unfold discreteKallenLehmannEuclid
  have h_zero : (0 : ℂ) = ∑ _a : Fin N, (0 : ℂ) := by simp
  rw [h_zero]
  refine tendsto_finsetSum Finset.univ (fun a _ => ?_)
  simpa using (tendsto_euclidSpectralTwoPoint_timeShift_atTop_zero (hE a) x y).const_mul (w a : ℂ)

def weylEpsilon (α : Fin 2 → Fin 2) : ℂ :=
  if α 0 = 0 ∧ α 1 = 1 then 1
  else if α 0 = 1 ∧ α 1 = 0 then -1
  else 0

@[simp]
lemma weylEpsilon_zero_zero : weylEpsilon ![0, 0] = 0 := by simp [weylEpsilon]

@[simp]
lemma weylEpsilon_zero_one : weylEpsilon ![0, 1] = 1 := by simp [weylEpsilon]

@[simp]
lemma weylEpsilon_one_zero : weylEpsilon ![1, 0] = -1 := by simp [weylEpsilon]

@[simp]
lemma weylEpsilon_one_one : weylEpsilon ![1, 1] = 0 := by simp [weylEpsilon]

@[simp]
theorem weylEpsilon_comp_rev (α : Fin 2 → Fin 2) :
    weylEpsilon (α ∘ Fin.rev) = -weylEpsilon α := by
  rw [finTwo_eq_vecCons α, finTwo_comp_rev_vecCons]
  generalize α 0 = a
  generalize α 1 = b
  fin_cases a <;> fin_cases b <;>
    simp [weylEpsilon_zero_zero, weylEpsilon_zero_one,
          weylEpsilon_one_zero, weylEpsilon_one_one]

theorem sum_matrix_mul_weylEpsilon (M : Matrix (Fin 2) (Fin 2) ℂ) (α : Fin 2 → Fin 2) :
    (∑ β : Fin 2 → Fin 2, (∏ i : Fin 2, M (α i) (β i)) * weylEpsilon β) =
      M.det * weylEpsilon α := by
  rw [sum_fin_two_fun, Fin.sum_univ_two]
  simp only [Fin.sum_univ_two, Fin.prod_univ_two, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    weylEpsilon_zero_zero, weylEpsilon_zero_one,
    weylEpsilon_one_zero, weylEpsilon_one_one, Matrix.det_fin_two]
  rw [finTwo_eq_vecCons α]
  generalize α 0 = a
  generalize α 1 = b
  fin_cases a <;> fin_cases b <;>
    simp [weylEpsilon_zero_zero, weylEpsilon_zero_one,
          weylEpsilon_one_zero, weylEpsilon_one_one] <;>
    ring

@[simp]
theorem sum_leftWeylRep_mul_weylEpsilon (p : SL2C × SL2C) (α : Fin 2 → Fin 2) :
    (∑ β : Fin 2 → Fin 2,
      (∏ i : Fin 2, leftWeylRep.σ p (α i) (β i)) * weylEpsilon β) =
      weylEpsilon α := by
  change (∑ β : Fin 2 → Fin 2, (∏ i : Fin 2, p.1.1 (α i) (β i)) * weylEpsilon β) =
    weylEpsilon α
  rw [sum_matrix_mul_weylEpsilon p.1.1 α, p.1.2, one_mul]

def weylFermionConst : ∀ n : ℕ, (Fin n → Fin 2) → ℂ
  | 0, _ => 1
  | 2, α => weylEpsilon α
  | _, _ => 0

@[simp]
lemma weylFermionConst_zero (α : Fin 0 → Fin 2) : weylFermionConst 0 α = 1 := rfl

@[simp]
lemma weylFermionConst_one (α : Fin 1 → Fin 2) : weylFermionConst 1 α = 0 := rfl

@[simp]
lemma weylFermionConst_two (α : Fin 2 → Fin 2) : weylFermionConst 2 α = weylEpsilon α := rfl

@[simp]
lemma weylFermionConst_add_three (m : ℕ) (α : Fin (m + 3) → Fin 2) :
    weylFermionConst (m + 3) α = 0 := rfl

theorem sum_leftWeylRep_mul_weylFermionConst (n : ℕ) (p : SL2C × SL2C) (α : Fin n → Fin 2) :
    (∑ β : Fin n → Fin 2,
      (∏ i : Fin n, leftWeylRep.σ p (α i) (β i)) * weylFermionConst n β) =
      weylFermionConst n α := by
  match n with
  | 0 =>
    have hα : α = Fin.elim0 := Subsingleton.elim _ _
    subst hα
    simp [weylFermionConst]
  | 1 =>
    simp [weylFermionConst]
  | 2 =>
    exact sum_leftWeylRep_mul_weylEpsilon p α
  | m + 3 =>
    simp [weylFermionConst]

theorem weylFermionConst_eq_neg_one_pow_mul_rev (n : ℕ) (α : Fin n → Fin 2) :
    weylFermionConst n α =
      ((-1 : ℂ) ^ (n * (n - 1) / 2)) * weylFermionConst n (α ∘ Fin.rev) := by
  match n with
  | 0 =>
    simp [weylFermionConst]
  | 1 =>
    simp [weylFermionConst]
  | 2 =>
    rw [two_mul_two_sub_one_div_two, pow_one]
    change weylEpsilon α = (-1 : ℂ) * weylEpsilon (α ∘ Fin.rev)
    rw [weylEpsilon_comp_rev]
    ring
  | m + 3 =>
    simp [weylFermionConst]

def weylFermionS : SchwingerFamily (Fin 2) :=
  fun n α _ => weylFermionConst n α

def weylFermionH : ∀ n : ℕ, (Fin n → Fin 2) → (Fin n → Fin 4 → ℂ) → ℂ :=
  fun n α _ => weylFermionConst n α

noncomputable def weylFermionW : WightmanFamily (Fin 2) :=
  fun n α => weylFermionConst n α • schwartzIntegralCLM n

@[simp]
lemma weylFermionW_apply (n : ℕ) (α : Fin n → Fin 2)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    weylFermionW n α f = weylFermionConst n α * ∫ x : Fin n → Fin 4 → ℝ, f x := rfl

@[simp]
theorem weylFermionW_unitIntegralSchwartz (n : ℕ) (α : Fin n → Fin 2) :
    weylFermionW n α (unitIntegralSchwartz n) = weylFermionConst n α := by
  rw [weylFermionW_apply, integral_unitIntegralSchwartz, mul_one]

@[simp]
theorem weylFermionW_two_zero_one :
    weylFermionW 2 ![0, 1] (unitIntegralSchwartz 2) = 1 := by
  rw [weylFermionW_unitIntegralSchwartz, weylFermionConst_two, weylEpsilon_zero_one]

theorem weylFermionW_twoPoint_nondegenerate :
    ∃ (α : Fin 2 → Fin 2) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ),
      weylFermionW 2 α f ≠ 0 :=
  ⟨![0, 1], unitIntegralSchwartz 2, by rw [weylFermionW_two_zero_one]; exact one_ne_zero⟩

noncomputable def weylFermionTubeExtension : TubeExtension weylFermionW where
  H := weylFermionH
  analytic _ _ := analyticOn_const
  boundary n α f v _hv := by
    have h_eq : (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        weylFermionH n α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x) =
        fun _ => weylFermionConst n α * ∫ x : Fin n → Fin 4 → ℝ, f x := by
      ext t
      dsimp [weylFermionH]
      exact integral_const_mul (weylFermionConst n α) f
    rw [h_eq, weylFermionW_apply]
    exact tendsto_const_nhds

@[simp]
lemma weylFermionTubeExtension_H : weylFermionTubeExtension.H = weylFermionH := rfl

@[simp]
theorem schwingerFromTube_weylFermionTubeExtension :
    schwingerFromTube weylFermionTubeExtension = weylFermionS := rfl

theorem weylFermionTubeBoundaryInjective :
    TubeBoundaryInjective weylFermionTubeExtension := by
  intro n α hW _z _hz
  have h_unit := hW (unitIntegralSchwartz n)
  rwa [weylFermionW_unitIntegralSchwartz] at h_unit

theorem weylFermionTubeTranslationInvariant :
    TubeTranslationInvariant weylFermionTubeExtension :=
  fun _ _ _ _ _ => rfl

theorem weylFermionTubeCovariant :
    TubeCovariant leftWeylRep weylFermionTubeExtension := by
  intro n A z _hz _hAz α
  dsimp [weylFermionTubeExtension_H, weylFermionH, HolomorphicLorentzRep.rep_apply]
  exact (sum_leftWeylRep_mul_weylFermionConst n (A, sl2c_conj A) α).symm

theorem weylFermionTubeWeakLocality :
    TubeWeakLocality (-1) weylFermionTubeExtension := by
  intro n α z _hz
  dsimp [weylFermionTubeExtension_H, weylFermionH]
  exact weylFermionConst_eq_neg_one_pow_mul_rev n α

theorem weylFermionZeroMomentumSpectrumCondition :
    ZeroMomentumSpectrumCondition weylFermionW := by
  intro n α f h0
  rw [minkowskiFourier_eval_zero_n] at h0
  rw [weylFermionW_apply, h0, mul_zero]

theorem weylFermionPoincareCovariant :
    PoincareCovariant leftWeylRep weylFermionW := by
  intro n a A f f' hf' α
  have h_int : (∫ x : Fin n → Fin 4 → ℝ, f x) = ∫ x : Fin n → Fin 4 → ℝ, f' x := by
    have h_f : (fun x : Fin n → Fin 4 → ℝ => f x) =
        fun x => f' (fun i => poincareAct a A (x i)) := by
      ext x
      exact (hf' x).symm
    rw [h_f, integral_poincareAct_eq]
  have h_sum : ∀ β : Fin n → Fin 2,
      (∏ i : Fin n, leftWeylRep.rep A (α i) (β i)) * weylFermionW n β f =
        ((∏ i : Fin n, leftWeylRep.σ (A, sl2c_conj A) (α i) (β i)) *
          weylFermionConst n β) * ∫ x : Fin n → Fin 4 → ℝ, f' x := by
    intro β
    rw [weylFermionW_apply, h_int, HolomorphicLorentzRep.rep_apply, mul_assoc]
  simp_rw [h_sum, ← Finset.sum_mul]
  rw [weylFermionW_apply, sum_leftWeylRep_mul_weylFermionConst n (A, sl2c_conj A) α]

theorem weylFermionWeakLocality :
    WeakLocality (-1) weylFermionW := by
  intro n α f f' _hf_jost hf'
  rw [weylFermionW_apply, weylFermionW_apply]
  have h_f : (fun x : Fin n → Fin 4 → ℝ => f x) =
      fun x => f' (fun i => x (Fin.rev i)) := by
    ext x
    exact (hf' x).symm
  rw [h_f, integral_comp_rev, ← mul_assoc]
  congr 1
  exact weylFermionConst_eq_neg_one_pow_mul_rev n α

theorem weylFermion_spin_statistics_unconditional
    {η : ℂ} (hloc : WeakLocality η weylFermionW) :
    η = -1 :=
  leftWeyl_wightman_spin_statistics_unconditional weylFermionW
    weylFermionZeroMomentumSpectrumCondition weylFermionPoincareCovariant hloc
    weylFermionW_twoPoint_nondegenerate

theorem not_weylFermion_bosonic_weakLocality :
    ¬ WeakLocality 1 weylFermionW := by
  intro hbos
  have h := weylFermion_spin_statistics_unconditional hbos
  norm_num at h

noncomputable def multiPointKallenLehmannTube
    (n N : ℕ) (w : Fin N → ℝ) (E : Fin N → Fin (n - 1) → ℝ)
    (z : Fin n → Fin 4 → ℂ) : ℂ :=
  ∑ a : Fin N, (w a : ℂ) * spectralMultiPointTube n (E a) z

noncomputable def multiPointKallenLehmannEuclid
    (n N : ℕ) (w : Fin N → ℝ) (E : Fin N → Fin (n - 1) → ℝ)
    (x : Fin n → Fin 4 → ℝ) : ℂ :=
  ∑ a : Fin N, (w a : ℂ) * euclidSpectralMultiPoint n (E a) x

@[simp]
theorem multiPointKallenLehmannTube_wickEmbedN
    (n N : ℕ) (w : Fin N → ℝ) (E : Fin N → Fin (n - 1) → ℝ)
    (x : Fin n → Fin 4 → ℝ) :
    multiPointKallenLehmannTube n N w E (wickEmbedN n x) =
      multiPointKallenLehmannEuclid n N w E x := by
  unfold multiPointKallenLehmannTube multiPointKallenLehmannEuclid
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [spectralMultiPointTube_wickEmbedN]

theorem differentiable_multiPointKallenLehmannTube
    (n N : ℕ) (w : Fin N → ℝ) (E : Fin N → Fin (n - 1) → ℝ) :
    Differentiable ℂ (multiPointKallenLehmannTube n N w E) := by
  unfold multiPointKallenLehmannTube
  have h_term : ∀ a : Fin N,
      Differentiable ℂ (fun z => (w a : ℂ) * spectralMultiPointTube n (E a) z) :=
    fun a => (differentiable_const (w a : ℂ)).mul
      (differentiable_spectralMultiPointTube n (E a))
  fun_prop

theorem analyticOn_multiPointKallenLehmannTube
    (n N : ℕ) (w : Fin N → ℝ) (E : Fin N → Fin (n - 1) → ℝ)
    (s : Set (Fin n → Fin 4 → ℂ)) :
    AnalyticOn ℂ (multiPointKallenLehmannTube n N w E) s :=
  AnalyticOnNhd.analyticOn (fun z _ => by
    unfold multiPointKallenLehmannTube
    refine analyticAt_finset_sum_normed Finset.univ (fun a _ => ?_)
    exact analyticAt_const.mul (analyticAt_spectralMultiPointTube n (E a) z))

@[simp]
theorem multiPointKallenLehmannTube_add_const
    (n N : ℕ) (w : Fin N → ℝ) (E : Fin N → Fin (n - 1) → ℝ)
    (z : Fin n → Fin 4 → ℂ) (a : Fin 4 → ℂ) :
    multiPointKallenLehmannTube n N w E (fun k => z k + a) =
      multiPointKallenLehmannTube n N w E z := by
  unfold multiPointKallenLehmannTube
  refine Finset.sum_congr rfl (fun idx _ => ?_)
  rw [spectralMultiPointTube_add_const]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem vladimirov_H_zero_momentW (c : ℕ → ℂ) (n : ℕ) (α : Fin n → ι) :
    vladimirov_H (momentW (ι := ι) c) n α 0 = c n := by
  have h := W_n_eq_vladimirov_H_zero_mul_integral
    (momentZeroMomentumSpectrumCondition (ι := ι) c) n α (unitIntegralSchwartz n)
  rw [momentW_unitIntegralSchwartz, integral_unitIntegralSchwartz, mul_one] at h
  exact h.symm

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem vladimirovSchwinger_momentW (c : ℕ → ℂ) :
    vladimirovSchwinger (momentW (ι := ι) c) = momentS (ι := ι) c := by
  ext n α x
  rw [vladimirovSchwinger_eq_zero_eval (momentZeroMomentumSpectrumCondition (ι := ι) c),
      vladimirov_H_zero_momentW]
  rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem vladimirovSchwinger_vacW :
    vladimirovSchwinger (vacW (ι := ι)) = vacS (ι := ι) := by
  ext n α x
  rw [vladimirovSchwinger_eq_zero_eval (vacZeroMomentumSpectrumCondition (ι := ι))]
  have h := W_n_eq_vladimirov_H_zero_mul_integral
    (vacZeroMomentumSpectrumCondition (ι := ι)) n α (unitIntegralSchwartz n)
  rw [integral_unitIntegralSchwartz, mul_one] at h
  rw [← h]
  cases n with
  | zero =>
    rw [vacW_zero_apply, ← integral_fin0 (unitIntegralSchwartz 0), vacS_zero]
    exact integral_unitIntegralSchwartz 0
  | succ m =>
    simp [vacS_succ]

theorem vac_wightmanSesquilinear_eq_inner_osWavepacketVector
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (N : ℕ)
    (F F' : ∀ j : ℕ, (Fin j → ι) → SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (G : ∀ j k : ℕ, (Fin j → ι) → (Fin k → ι) →
      SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ)
    (hG : ∀ j k α α' (x : Fin (j + k) → Fin 4 → ℝ),
      G j k α α' x =
        (starRingEnd ℂ) (F j α (fun i => x (Fin.castAdd k (Fin.rev i)))) *
          F' k α' (fun i => x (Fin.natAdd j i))) :
    (∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          vacW (j + k) (Fin.append (β ∘ Fin.rev) α') (G j k α α')) =
      ⟪osWavepacketVector (vacOSData R S) N F,
       osWavepacketVector (vacOSData R S) N F'⟫_ℂ :=
  wightmanSesquilinear_eq_inner_osWavepacketVector
    (vacOSData R S) vacZeroMomentumSpectrumCondition vladimirovSchwinger_vacW.symm N F F' G hG

theorem z2Free_wightmanSesquilinear_eq_inner_osWavepacketVector
    (N : ℕ)
    (F F' : ∀ j : ℕ, (Fin j → Unit) → SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (G : ∀ j k : ℕ, (Fin j → Unit) → (Fin k → Unit) →
      SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ)
    (hG : ∀ j k α α' (x : Fin (j + k) → Fin 4 → ℝ),
      G j k α α' x =
        (starRingEnd ℂ) (F j α (fun i => x (Fin.castAdd k (Fin.rev i)))) *
          F' k α' (fun i => x (Fin.natAdd j i))) :
    (∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ∑ α : Fin j → Unit, ∑ α' : Fin k → Unit, ∑ β : Fin j → Unit,
        (∏ i : Fin j, trivialStarStructure.C (α i) (β i)) *
          z2FreeW (j + k) (Fin.append (β ∘ Fin.rev) α') (G j k α α')) =
      ⟪osWavepacketVector z2FreeOSData N F,
       osWavepacketVector z2FreeOSData N F'⟫_ℂ :=
  wightmanSesquilinear_eq_inner_osWavepacketVector
    z2FreeOSData (momentZeroMomentumSpectrumCondition z2FreeCoeff)
    (vladimirovSchwinger_momentW z2FreeCoeff).symm N F F' G hG

theorem z2Free_wightmanSesquilinear_diag_eq_norm_sq_osWavepacketVector
    (N : ℕ)
    (F : ∀ j : ℕ, (Fin j → Unit) → SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (G : ∀ j k : ℕ, (Fin j → Unit) → (Fin k → Unit) →
      SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ)
    (hG : ∀ j k α α' (x : Fin (j + k) → Fin 4 → ℝ),
      G j k α α' x =
        (starRingEnd ℂ) (F j α (fun i => x (Fin.castAdd k (Fin.rev i)))) *
          F k α' (fun i => x (Fin.natAdd j i))) :
    (∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ∑ α : Fin j → Unit, ∑ α' : Fin k → Unit, ∑ β : Fin j → Unit,
        (∏ i : Fin j, trivialStarStructure.C (α i) (β i)) *
          z2FreeW (j + k) (Fin.append (β ∘ Fin.rev) α') (G j k α α')) =
      (‖osWavepacketVector z2FreeOSData N F‖ ^ 2 : ℂ) :=
  wightmanSesquilinear_diag_eq_norm_sq_osWavepacketVector
    z2FreeOSData (momentZeroMomentumSpectrumCondition z2FreeCoeff)
    (vladimirovSchwinger_momentW z2FreeCoeff).symm N F G hG

@[simp]
theorem sum_rightWeylRep_mul_weylEpsilon (p : SL2C × SL2C) (α : Fin 2 → Fin 2) :
    (∑ β : Fin 2 → Fin 2,
      (∏ i : Fin 2, rightWeylRep.σ p (α i) (β i)) * weylEpsilon β) =
      weylEpsilon α := by
  change (∑ β : Fin 2 → Fin 2, (∏ i : Fin 2, p.2.1 (α i) (β i)) * weylEpsilon β) =
    weylEpsilon α
  rw [sum_matrix_mul_weylEpsilon p.2.1 α, p.2.2, one_mul]

@[simp]
theorem star_weylEpsilon (α : Fin 2 → Fin 2) :
    star (weylEpsilon α) = weylEpsilon α := by
  rw [finTwo_eq_vecCons α]
  generalize α 0 = a
  generalize α 1 = b
  fin_cases a <;> fin_cases b <;>
    simp [weylEpsilon_zero_zero, weylEpsilon_zero_one,
          weylEpsilon_one_zero, weylEpsilon_one_one]

noncomputable def diracEpsilon (α : Fin 2 → Fin 2 ⊕ Fin 2) : ℂ :=
  match α 0, α 1 with
  | Sum.inl a, Sum.inl b => Complex.I * weylEpsilon ![a, b]
  | Sum.inr a, Sum.inr b => Complex.I * weylEpsilon ![a, b]
  | _, _ => 0

@[simp]
lemma diracEpsilon_inl_inl (a b : Fin 2) :
    diracEpsilon ![Sum.inl a, Sum.inl b] = Complex.I * weylEpsilon ![a, b] := rfl

@[simp]
lemma diracEpsilon_inr_inr (a b : Fin 2) :
    diracEpsilon ![Sum.inr a, Sum.inr b] = Complex.I * weylEpsilon ![a, b] := rfl

@[simp]
lemma diracEpsilon_inl_inr (a b : Fin 2) :
    diracEpsilon ![Sum.inl a, Sum.inr b] = 0 := rfl

@[simp]
lemma diracEpsilon_inr_inl (a b : Fin 2) :
    diracEpsilon ![Sum.inr a, Sum.inl b] = 0 := rfl

@[simp]
lemma diracEpsilon_comp_inl (γ : Fin 2 → Fin 2) :
    diracEpsilon (Sum.inl ∘ γ) = Complex.I * weylEpsilon γ := by
  change diracEpsilon ![Sum.inl (γ 0), Sum.inl (γ 1)] = Complex.I * weylEpsilon γ
  rw [diracEpsilon_inl_inl, ← finTwo_eq_vecCons γ]

@[simp]
lemma diracEpsilon_comp_inr (γ : Fin 2 → Fin 2) :
    diracEpsilon (Sum.inr ∘ γ) = Complex.I * weylEpsilon γ := by
  change diracEpsilon ![Sum.inr (γ 0), Sum.inr (γ 1)] = Complex.I * weylEpsilon γ
  rw [diracEpsilon_inr_inr, ← finTwo_eq_vecCons γ]

@[simp]
theorem diracEpsilon_comp_rev (α : Fin 2 → Fin 2 ⊕ Fin 2) :
    diracEpsilon (α ∘ Fin.rev) = -diracEpsilon α := by
  rw [finTwo_eq_vecCons α, finTwo_comp_rev_vecCons]
  rcases α 0 with a | a <;> rcases α 1 with b | b
  · rw [diracEpsilon_inl_inl, diracEpsilon_inl_inl]
    have hrev := weylEpsilon_comp_rev ![a, b]
    rw [finTwo_comp_rev_vecCons] at hrev
    rw [hrev]
    ring
  · simp
  · simp
  · rw [diracEpsilon_inr_inr, diracEpsilon_inr_inr]
    have hrev := weylEpsilon_comp_rev ![a, b]
    rw [finTwo_comp_rev_vecCons] at hrev
    rw [hrev]
    ring

@[simp]
theorem diracEpsilon_comp_swap (α : Fin 2 → Fin 2 ⊕ Fin 2) :
    diracEpsilon (Sum.swap ∘ α) = diracEpsilon α := by
  rw [finTwo_eq_vecCons α]
  rcases α 0 with a | a <;> rcases α 1 with b | b <;> rfl

theorem star_diracEpsilon (α : Fin 2 → Fin 2 ⊕ Fin 2) :
    star (diracEpsilon α) = diracEpsilon (Sum.swap ∘ α ∘ Fin.rev) := by
  rw [diracEpsilon_comp_swap, diracEpsilon_comp_rev, finTwo_eq_vecCons α]
  rcases α 0 with a | a <;> rcases α 1 with b | b
  · rw [diracEpsilon_inl_inl, star_mul', Complex.star_def, Complex.conj_I,
        ← Complex.star_def, star_weylEpsilon]
    ring
  · simp
  · simp
  · rw [diracEpsilon_inr_inr, star_mul', Complex.star_def, Complex.conj_I,
        ← Complex.star_def, star_weylEpsilon]
    ring

@[simp]
theorem sum_diracRep_mul_diracEpsilon (p : SL2C × SL2C) (α : Fin 2 → Fin 2 ⊕ Fin 2) :
    (∑ β : Fin 2 → Fin 2 ⊕ Fin 2,
      (∏ i : Fin 2, diracRep.σ p (α i) (β i)) * diracEpsilon β) =
      diracEpsilon α := by
  rw [finTwo_eq_vecCons α]
  rcases α 0 with a | a <;> rcases α 1 with b | b
  · have h_inl : (![Sum.inl a, Sum.inl b] : Fin 2 → Fin 2 ⊕ Fin 2) =
        Sum.inl ∘ (![a, b] : Fin 2 → Fin 2) := by
      ext i
      fin_cases i <;> rfl
    rw [h_inl]
    have h_sum := sum_directSumRep_inl_two leftWeylRep rightWeylRep p.1 p.2
      diracEpsilon ![a, b]
    change (∑ β : Fin 2 → Fin 2 ⊕ Fin 2,
      (∏ i : Fin 2, (directSumRep leftWeylRep rightWeylRep).σ (p.1, p.2)
        (Sum.inl (![a, b] i)) (β i)) * diracEpsilon β) = _
    rw [h_sum]
    simp_rw [diracEpsilon_comp_inl, ← mul_assoc, mul_comm _ Complex.I, mul_assoc]
    rw [← Finset.mul_sum, sum_leftWeylRep_mul_weylEpsilon p ![a, b] ]
  · rw [diracEpsilon_inl_inr]
    refine Finset.sum_eq_zero (fun β _ => ?_)
    rw [Fin.prod_univ_two, finTwo_eq_vecCons β]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    rcases β 0 with x | x <;> rcases β 1 with y | y
    · have h0 : diracRep.σ p (Sum.inr b) (Sum.inl y) = 0 := rfl
      rw [h0, mul_zero, zero_mul]
    · rw [diracEpsilon_inl_inr, mul_zero]
    · have h0 : diracRep.σ p (Sum.inl a) (Sum.inr x) = 0 := rfl
      rw [h0, zero_mul, zero_mul]
    · have h0 : diracRep.σ p (Sum.inl a) (Sum.inr x) = 0 := rfl
      rw [h0, zero_mul, zero_mul]
  · rw [diracEpsilon_inr_inl]
    refine Finset.sum_eq_zero (fun β _ => ?_)
    rw [Fin.prod_univ_two, finTwo_eq_vecCons β]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    rcases β 0 with x | x <;> rcases β 1 with y | y
    · have h0 : diracRep.σ p (Sum.inr a) (Sum.inl x) = 0 := rfl
      rw [h0, zero_mul, zero_mul]
    · have h0 : diracRep.σ p (Sum.inr a) (Sum.inl x) = 0 := rfl
      rw [h0, zero_mul, zero_mul]
    · rw [diracEpsilon_inr_inl, mul_zero]
    · have h0 : diracRep.σ p (Sum.inl b) (Sum.inr y) = 0 := rfl
      rw [h0, mul_zero, zero_mul]
  · have h_inr : (![Sum.inr a, Sum.inr b] : Fin 2 → Fin 2 ⊕ Fin 2) =
        Sum.inr ∘ (![a, b] : Fin 2 → Fin 2) := by
      ext i
      fin_cases i <;> rfl
    rw [h_inr]
    have h_sum := sum_directSumRep_inr_two leftWeylRep rightWeylRep p.1 p.2
      diracEpsilon ![a, b]
    change (∑ β : Fin 2 → Fin 2 ⊕ Fin 2,
      (∏ i : Fin 2, (directSumRep leftWeylRep rightWeylRep).σ (p.1, p.2)
        (Sum.inr (![a, b] i)) (β i)) * diracEpsilon β) = _
    rw [h_sum]
    simp_rw [diracEpsilon_comp_inr, ← mul_assoc, mul_comm _ Complex.I, mul_assoc]
    rw [← Finset.mul_sum, sum_rightWeylRep_mul_weylEpsilon p ![a, b] ]

noncomputable def diracFermionConst : ∀ n : ℕ, (Fin n → Fin 2 ⊕ Fin 2) → ℂ
  | 0, _ => 1
  | 2, α => diracEpsilon α
  | _, _ => 0

@[simp]
lemma diracFermionConst_zero (α : Fin 0 → Fin 2 ⊕ Fin 2) : diracFermionConst 0 α = 1 := rfl

@[simp]
lemma diracFermionConst_one (α : Fin 1 → Fin 2 ⊕ Fin 2) : diracFermionConst 1 α = 0 := rfl

@[simp]
lemma diracFermionConst_two (α : Fin 2 → Fin 2 ⊕ Fin 2) :
    diracFermionConst 2 α = diracEpsilon α := rfl

@[simp]
lemma diracFermionConst_add_three (m : ℕ) (α : Fin (m + 3) → Fin 2 ⊕ Fin 2) :
    diracFermionConst (m + 3) α = 0 := rfl

theorem sum_diracRep_mul_diracFermionConst
    (n : ℕ) (p : SL2C × SL2C) (α : Fin n → Fin 2 ⊕ Fin 2) :
    (∑ β : Fin n → Fin 2 ⊕ Fin 2,
      (∏ i : Fin n, diracRep.σ p (α i) (β i)) * diracFermionConst n β) =
      diracFermionConst n α := by
  match n with
  | 0 =>
    have hα : α = Fin.elim0 := Subsingleton.elim _ _
    subst hα
    simp [diracFermionConst]
  | 1 =>
    simp [diracFermionConst]
  | 2 =>
    exact sum_diracRep_mul_diracEpsilon p α
  | m + 3 =>
    simp [diracFermionConst]

theorem diracFermionConst_eq_neg_one_pow_mul_rev
    (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) :
    diracFermionConst n α =
      ((-1 : ℂ) ^ (n * (n - 1) / 2)) * diracFermionConst n (α ∘ Fin.rev) := by
  match n with
  | 0 =>
    simp [diracFermionConst]
  | 1 =>
    simp [diracFermionConst]
  | 2 =>
    rw [two_mul_two_sub_one_div_two, pow_one]
    change diracEpsilon α = (-1 : ℂ) * diracEpsilon (α ∘ Fin.rev)
    rw [diracEpsilon_comp_rev]
    ring
  | m + 3 =>
    simp [diracFermionConst]

lemma chiralDoubleStarStructure_C_apply (R : HolomorphicLorentzRep ι) (hR : R.HasRealConj)
    (x y : ι ⊕ ι) :
    (chiralDoubleStarStructure R hR).C x y = if y = x.swap then 1 else 0 := by
  rcases x with i₁ | i₂ <;> rcases y with j₁ | j₂
  · simp [chiralDoubleStarStructure]
  · change (1 : Matrix ι ι ℂ) i₁ j₂ = if Sum.inr j₂ = Sum.inr i₁ then 1 else 0
    by_cases hij : i₁ = j₂
    · subst hij; simp
    · have hne : j₂ ≠ i₁ := Ne.symm hij
      simp [hij, hne]
  · change (1 : Matrix ι ι ℂ) i₂ j₁ = if Sum.inl j₁ = Sum.inl i₂ then 1 else 0
    by_cases hij : i₂ = j₁
    · subst hij; simp
    · have hne : j₁ ≠ i₂ := Ne.symm hij
      simp [hij, hne]
  · simp [chiralDoubleStarStructure]

lemma prod_chiralDoubleStarStructure_C (R : HolomorphicLorentzRep ι) (hR : R.HasRealConj)
    (n : ℕ) (α β : Fin n → ι ⊕ ι) :
    (∏ i : Fin n, (chiralDoubleStarStructure R hR).C (α i) (β i)) =
      if β = Sum.swap ∘ α then 1 else 0 := by
  simp_rw [chiralDoubleStarStructure_C_apply]
  by_cases hβ : β = Sum.swap ∘ α
  · subst hβ
    rw [if_pos rfl]
    exact Finset.prod_eq_one (fun i _ => if_pos rfl)
  · rw [if_neg hβ]
    have h_ex : ∃ i : Fin n, β i ≠ (α i).swap := by
      by_contra h_all
      exact hβ (funext fun i => Classical.not_not.mp fun hni => h_all ⟨i, hni⟩)
    rcases h_ex with ⟨i₀, hi₀⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i₀) (if_neg hi₀)

@[simp]
lemma sum_prod_chiralDoubleStarStructure_C_mul (R : HolomorphicLorentzRep ι) (hR : R.HasRealConj)
    (n : ℕ) (α : Fin n → ι ⊕ ι) (G : (Fin n → ι ⊕ ι) → ℂ) :
    (∑ β : Fin n → ι ⊕ ι,
      (∏ i : Fin n, (chiralDoubleStarStructure R hR).C (α i) (β i)) * G β) =
      G (Sum.swap ∘ α) := by
  simp_rw [prod_chiralDoubleStarStructure_C, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

theorem star_diracFermionConst (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) :
    star (diracFermionConst n α) =
      diracFermionConst n ((Sum.swap ∘ α) ∘ Fin.rev) := by
  match n with
  | 0 =>
    simp [diracFermionConst]
  | 1 =>
    simp [diracFermionConst]
  | 2 =>
    exact star_diracEpsilon α
  | m + 3 =>
    simp [diracFermionConst]

noncomputable def diracFermionS : SchwingerFamily (Fin 2 ⊕ Fin 2) :=
  fun n α _ => diracFermionConst n α

noncomputable def diracFermionH :
    ∀ n : ℕ, (Fin n → Fin 2 ⊕ Fin 2) → (Fin n → Fin 4 → ℂ) → ℂ :=
  fun n α _ => diracFermionConst n α

noncomputable def diracFermionW : WightmanFamily (Fin 2 ⊕ Fin 2) :=
  fun n α => diracFermionConst n α • schwartzIntegralCLM n

@[simp]
lemma diracFermionW_apply (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    diracFermionW n α f = diracFermionConst n α * ∫ x : Fin n → Fin 4 → ℝ, f x := rfl

@[simp]
theorem diracFermionW_unitIntegralSchwartz (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) :
    diracFermionW n α (unitIntegralSchwartz n) = diracFermionConst n α := by
  rw [diracFermionW_apply, integral_unitIntegralSchwartz, mul_one]

@[simp]
theorem diracFermionW_two_inl_zero_one :
    diracFermionW 2 ![Sum.inl 0, Sum.inl 1] (unitIntegralSchwartz 2) = Complex.I := by
  rw [diracFermionW_unitIntegralSchwartz, diracFermionConst_two,
      diracEpsilon_inl_inl, weylEpsilon_zero_one, mul_one]

theorem diracFermionW_twoPoint_nondegenerate :
    ∃ (α : Fin 2 → Fin 2 ⊕ Fin 2) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ),
      diracFermionW 2 α f ≠ 0 :=
  ⟨![Sum.inl 0, Sum.inl 1], unitIntegralSchwartz 2, by
    rw [diracFermionW_two_inl_zero_one]
    exact Complex.I_ne_zero⟩

noncomputable def diracFermionTubeExtension : TubeExtension diracFermionW where
  H := diracFermionH
  analytic _ _ := analyticOn_const
  boundary n α f v _hv := by
    have h_eq : (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        diracFermionH n α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x) =
        fun _ => diracFermionConst n α * ∫ x : Fin n → Fin 4 → ℝ, f x := by
      ext t
      dsimp [diracFermionH]
      exact integral_const_mul (diracFermionConst n α) f
    rw [h_eq, diracFermionW_apply]
    exact tendsto_const_nhds

@[simp]
lemma diracFermionTubeExtension_H : diracFermionTubeExtension.H = diracFermionH := rfl

@[simp]
theorem schwingerFromTube_diracFermionTubeExtension :
    schwingerFromTube diracFermionTubeExtension = diracFermionS := rfl

theorem diracFermionTubeBoundaryInjective :
    TubeBoundaryInjective diracFermionTubeExtension := by
  intro n α hW _z _hz
  have h_unit := hW (unitIntegralSchwartz n)
  rwa [diracFermionW_unitIntegralSchwartz] at h_unit

theorem diracFermionTubeTranslationInvariant :
    TubeTranslationInvariant diracFermionTubeExtension :=
  fun _ _ _ _ _ => rfl

theorem diracFermionTubeCovariant :
    TubeCovariant diracRep diracFermionTubeExtension := by
  intro n A z _hz _hAz α
  dsimp [diracFermionTubeExtension_H, diracFermionH, HolomorphicLorentzRep.rep_apply]
  exact (sum_diracRep_mul_diracFermionConst n (A, sl2c_conj A) α).symm

theorem diracFermionTubeWickHermiticity :
    TubeWickHermiticity diracStarStructure diracFermionTubeExtension := by
  intro n α z _hz _hz_rev
  dsimp [diracFermionTubeExtension_H, diracFermionH, diracStarStructure]
  rw [sum_prod_chiralDoubleStarStructure_C_mul leftWeylRep leftWeylRep_hasRealConj
      n α (fun β => diracFermionConst n (β ∘ Fin.rev))]
  exact star_diracFermionConst n α

theorem diracFermionOSHermiticity :
    OSHermiticity diracStarStructure diracFermionS :=
  schwingerFromTube_os_hermiticity diracStarStructure diracFermionTubeExtension
    diracFermionTubeWickHermiticity

theorem diracFermionTubeWeakLocality :
    TubeWeakLocality (-1) diracFermionTubeExtension := by
  intro n α z _hz
  dsimp [diracFermionTubeExtension_H, diracFermionH]
  exact diracFermionConst_eq_neg_one_pow_mul_rev n α

theorem diracFermionZeroMomentumSpectrumCondition :
    ZeroMomentumSpectrumCondition diracFermionW := by
  intro n α f h0
  rw [minkowskiFourier_eval_zero_n] at h0
  rw [diracFermionW_apply, h0, mul_zero]

theorem diracFermionPoincareCovariant :
    PoincareCovariant diracRep diracFermionW := by
  intro n a A f f' hf' α
  have h_int : (∫ x : Fin n → Fin 4 → ℝ, f x) = ∫ x : Fin n → Fin 4 → ℝ, f' x := by
    have h_f : (fun x : Fin n → Fin 4 → ℝ => f x) =
        fun x => f' (fun i => poincareAct a A (x i)) := by
      ext x
      exact (hf' x).symm
    rw [h_f, integral_poincareAct_eq]
  have h_sum : ∀ β : Fin n → Fin 2 ⊕ Fin 2,
      (∏ i : Fin n, diracRep.rep A (α i) (β i)) * diracFermionW n β f =
        ((∏ i : Fin n, diracRep.σ (A, sl2c_conj A) (α i) (β i)) *
          diracFermionConst n β) * ∫ x : Fin n → Fin 4 → ℝ, f' x := by
    intro β
    rw [diracFermionW_apply, h_int, HolomorphicLorentzRep.rep_apply, mul_assoc]
  simp_rw [h_sum, ← Finset.sum_mul]
  rw [diracFermionW_apply, sum_diracRep_mul_diracFermionConst n (A, sl2c_conj A) α]

theorem diracFermionWeakLocality :
    WeakLocality (-1) diracFermionW := by
  intro n α f f' _hf_jost hf'
  rw [diracFermionW_apply, diracFermionW_apply]
  have h_f : (fun x : Fin n → Fin 4 → ℝ => f x) =
      fun x => f' (fun i => x (Fin.rev i)) := by
    ext x
    exact (hf' x).symm
  rw [h_f, integral_comp_rev, ← mul_assoc]
  congr 1
  exact diracFermionConst_eq_neg_one_pow_mul_rev n α

theorem diracFermionPCT :
    WightmanPCT (-1) diracRep diracFermionW :=
  wightman_pct_theorem diracRep diracFermionW
    diracFermionZeroMomentumSpectrumCondition diracFermionPoincareCovariant diracFermionWeakLocality

theorem diracFermion_spin_statistics_unconditional
    {η : ℂ} (hloc : WeakLocality η diracFermionW) :
    η = -1 :=
  dirac_wightman_spin_statistics_unconditional diracFermionW
    diracFermionZeroMomentumSpectrumCondition diracFermionPoincareCovariant hloc
    diracFermionW_twoPoint_nondegenerate

theorem not_diracFermion_bosonic_weakLocality :
    ¬ WeakLocality 1 diracFermionW := by
  intro hbos
  have h := diracFermion_spin_statistics_unconditional hbos
  norm_num at h

@[simp]
theorem tubeWickTimeDiff_two_neg_comp_rev (z : Fin 2 → Fin 4 → ℂ) :
    tubeWickTimeDiff 2 (-(z ∘ Fin.rev)) 0 (by decide) =
      tubeWickTimeDiff 2 z 0 (by decide) := by
  unfold tubeWickTimeDiff
  have h0 : Fin.rev (0 : Fin 2) = 1 := rfl
  have h1 : Fin.rev (1 : Fin 2) = 0 := rfl
  change -Complex.I * (-z (Fin.rev 1) 0 - -z (Fin.rev 0) 0) =
    -Complex.I * (z 1 0 - z 0 0)
  rw [h0, h1]
  ring

@[simp]
theorem spectralTwoPointTube_neg_comp_rev (E : ℝ) (z : Fin 2 → Fin 4 → ℂ) :
    spectralTwoPointTube E (-(z ∘ Fin.rev)) = spectralTwoPointTube E z := by
  unfold spectralTwoPointTube
  rw [tubeWickTimeDiff_two_neg_comp_rev]

@[simp]
theorem discreteKallenLehmannTube_neg_comp_rev
    (N : ℕ) (w E : Fin N → ℝ) (z : Fin 2 → Fin 4 → ℂ) :
    discreteKallenLehmannTube N w E (-(z ∘ Fin.rev)) =
      discreteKallenLehmannTube N w E z := by
  unfold discreteKallenLehmannTube
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [spectralTwoPointTube_neg_comp_rev]

@[simp]
theorem euclidSpectralTwoPoint_neg_comp_rev (E : ℝ) (x : Fin 2 → Fin 4 → ℝ) :
    euclidSpectralTwoPoint E (-(x ∘ Fin.rev)) = euclidSpectralTwoPoint E x := by
  unfold euclidSpectralTwoPoint
  have h0 : Fin.rev (0 : Fin 2) = 1 := rfl
  have h1 : Fin.rev (1 : Fin 2) = 0 := rfl
  change laplaceExp E (((-x (Fin.rev 1) 0 - -x (Fin.rev 0) 0 : ℝ) : ℂ)) =
    laplaceExp E ((x 1 0 - x 0 0 : ℝ) : ℂ)
  rw [h0, h1]
  congr 2
  ring

@[simp]
theorem discreteKallenLehmannEuclid_neg_comp_rev
    (N : ℕ) (w E : Fin N → ℝ) (x : Fin 2 → Fin 4 → ℝ) :
    discreteKallenLehmannEuclid N w E (-(x ∘ Fin.rev)) =
      discreteKallenLehmannEuclid N w E x := by
  unfold discreteKallenLehmannEuclid
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [euclidSpectralTwoPoint_neg_comp_rev]

@[simp]
theorem tubeWickTimeDiff_two_star_rev (z : Fin 2 → Fin 4 → ℂ) :
    tubeWickTimeDiff 2 (fun i μ => star (z (Fin.rev i) μ)) 0 (by decide) =
      star (tubeWickTimeDiff 2 z 0 (by decide)) := by
  unfold tubeWickTimeDiff
  have h0 : Fin.rev (0 : Fin 2) = 1 := rfl
  have h1 : Fin.rev (1 : Fin 2) = 0 := rfl
  change -Complex.I * (star (z (Fin.rev 1) 0) - star (z (Fin.rev 0) 0)) =
    star (-Complex.I * (z 1 0 - z 0 0))
  rw [h0, h1, star_mul', star_sub, Complex.star_def, map_neg, Complex.conj_I, ← Complex.star_def]
  ring

theorem star_spectralTwoPointTube (E : ℝ) (z : Fin 2 → Fin 4 → ℂ) :
    star (spectralTwoPointTube E z) =
      spectralTwoPointTube E (fun i μ => star (z (Fin.rev i) μ)) := by
  unfold spectralTwoPointTube
  rw [tubeWickTimeDiff_two_star_rev, laplaceExp_star]

theorem star_discreteKallenLehmannTube
    (N : ℕ) (w E : Fin N → ℝ) (z : Fin 2 → Fin 4 → ℂ) :
    star (discreteKallenLehmannTube N w E z) =
      discreteKallenLehmannTube N w E (fun i μ => star (z (Fin.rev i) μ)) := by
  unfold discreteKallenLehmannTube
  rw [star_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [star_mul', Complex.star_def, Complex.conj_ofReal, ← Complex.star_def,
      star_spectralTwoPointTube]

theorem norm_discreteKallenLehmannTube_le
    {N : ℕ} {w : Fin N → ℝ} (hw : ∀ a : Fin N, 0 ≤ w a)
    {E : Fin N → ℝ} (hE : ∀ a : Fin N, 0 ≤ E a)
    {z : Fin 2 → Fin 4 → ℂ} (hz : z ∈ forward_tube_n 2) :
    ‖discreteKallenLehmannTube N w E z‖ ≤ ∑ a : Fin N, w a := by
  unfold discreteKallenLehmannTube
  refine (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum (fun a _ => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw a)]
  have h_le := norm_spectralTwoPointTube_le_one (hE a) hz
  nlinarith [hw a]

theorem norm_multiPointKallenLehmannTube_le
    {n N : ℕ} {w : Fin N → ℝ} (hw : ∀ a : Fin N, 0 ≤ w a)
    {E : Fin N → Fin (n - 1) → ℝ} (hE : ∀ (a : Fin N) (i : Fin (n - 1)), 0 ≤ E a i)
    {z : Fin n → Fin 4 → ℂ} (hz : z ∈ forward_tube_n n) :
    ‖multiPointKallenLehmannTube n N w E z‖ ≤ ∑ a : Fin N, w a := by
  unfold multiPointKallenLehmannTube
  refine (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum (fun a _ => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw a)]
  have h_le := norm_spectralMultiPointTube_le_one (hE a) hz
  nlinarith [hw a]

theorem vladimirovKernel_diracRep_one_self_eq_zero
    (W : WightmanFamily (Fin 2 ⊕ Fin 2))
    (hspec : ZeroMomentumSpectrumCondition W) (hP : PoincareCovariant diracRep W)
    (c : Fin 2 ⊕ Fin 2) :
    vladimirovKernel diracStarStructure W 1 1 (fun _ => c) (fun _ => c) = 0 := by
  unfold vladimirovKernel
  change (∑ β : Fin 1 → Fin 2 ⊕ Fin 2,
    (∏ i : Fin 1, (chiralDoubleStarStructure leftWeylRep leftWeylRep_hasRealConj).C
      c (β i)) *
      vladimirov_H W (1 + 1) (Fin.append (β ∘ Fin.rev) (fun _ => c)) 0) = 0
  rw [sum_prod_chiralDoubleStarStructure_C_mul leftWeylRep leftWeylRep_hasRealConj
      1 (fun _ => c) (fun β => vladimirov_H W (1 + 1) (Fin.append (β ∘ Fin.rev) (fun _ => c)) 0)]
  have h_idx : Fin.append ((Sum.swap ∘ fun _ : Fin 1 => c) ∘ Fin.rev) (fun _ : Fin 1 => c) =
      ![c.swap, c] := by
    ext i
    fin_cases i <;> rfl
  rw [h_idx]
  rcases c with a | a
  · exact vladimirov_H_zero_diracRep_inr_inl_eq_zero W hspec hP a a
  · exact vladimirov_H_zero_diracRep_inl_inr_eq_zero W hspec hP a a

theorem vacPositivity_of_osData (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    Positivity S (vacW (ι := ι)) :=
  positivity_of_osReflectionPositiveData (vacOSData R S)
    vacZeroMomentumSpectrumCondition vladimirovSchwinger_vacW.symm

theorem z2FreePositivity_of_osData :
    Positivity trivialStarStructure z2FreeW :=
  positivity_of_osReflectionPositiveData z2FreeOSData
    (momentZeroMomentumSpectrumCondition z2FreeCoeff)
    (vladimirovSchwinger_momentW z2FreeCoeff).symm

noncomputable def vacEuclideanTubeBridgeOfOSData
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) :
    OSEuclideanTubeBridge R S η vacS :=
  vladimirovEuclideanTubeBridgeOfOSData R S (vacOSData R S) vacW
    vacZeroMomentumSpectrumCondition (vacPoincareCovariant R) (vacWeakLocality η)
    (fun n α x _ => by rw [vladimirovSchwinger_vacW]; rfl)

noncomputable def z2FreeEuclideanTubeBridgeOfOSData :
    OSEuclideanTubeBridge trivialRep trivialStarStructure 1 z2FreeS :=
  vladimirovEuclideanTubeBridgeOfOSData trivialRep trivialStarStructure
    z2FreeOSData z2FreeW
    (momentZeroMomentumSpectrumCondition z2FreeCoeff)
    (momentPoincareCovariant z2FreeCoeff)
    (momentWeakLocality z2FreeCoeff)
    (fun n α x _ => by
      change z2FreeS n α x = vladimirovSchwinger (momentW z2FreeCoeff) n α x
      rw [vladimirovSchwinger_momentW]
      rfl)

theorem wightman_diracRep_eq_zero_of_positivity
    (W : WightmanFamily (Fin 2 ⊕ Fin 2))
    (hspec : ZeroMomentumSpectrumCondition W) (hP : PoincareCovariant diracRep W)
    (hpos : Positivity diracStarStructure W)
    (n : ℕ) (hn : 1 ≤ n) (α : Fin n → Fin 2 ⊕ Fin 2)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    W n α f = 0 :=
  wightman_eq_zero_of_onePoint_vladimirovKernel_eq_zero diracStarStructure W hspec hpos
    (vladimirovKernel_diracRep_one_self_eq_zero W hspec hP) n hn α f

theorem not_diracFermionW_positivity :
    ¬ Positivity diracStarStructure diracFermionW := by
  intro hpos
  rcases diracFermionW_twoPoint_nondegenerate with ⟨α, f, hne⟩
  exact hne (wightman_diracRep_eq_zero_of_positivity diracFermionW
    diracFermionZeroMomentumSpectrumCondition diracFermionPoincareCovariant hpos 2 (by omega) α f)

@[simp]
theorem vladimirov_H_zero_weylFermionW (n : ℕ) (α : Fin n → Fin 2) :
    vladimirov_H weylFermionW n α 0 = weylFermionConst n α := by
  have h := W_n_eq_vladimirov_H_zero_mul_integral
    weylFermionZeroMomentumSpectrumCondition n α (unitIntegralSchwartz n)
  rw [weylFermionW_unitIntegralSchwartz, integral_unitIntegralSchwartz, mul_one] at h
  exact h.symm

@[simp]
theorem vladimirovSchwinger_weylFermionW :
    vladimirovSchwinger weylFermionW = weylFermionS := by
  ext n α x
  rw [vladimirovSchwinger_eq_zero_eval weylFermionZeroMomentumSpectrumCondition,
      vladimirov_H_zero_weylFermionW]
  rfl

@[simp]
theorem vladimirov_H_zero_diracFermionW (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) :
    vladimirov_H diracFermionW n α 0 = diracFermionConst n α := by
  have h := W_n_eq_vladimirov_H_zero_mul_integral
    diracFermionZeroMomentumSpectrumCondition n α (unitIntegralSchwartz n)
  rw [diracFermionW_unitIntegralSchwartz, integral_unitIntegralSchwartz, mul_one] at h
  exact h.symm

@[simp]
theorem vladimirovSchwinger_diracFermionW :
    vladimirovSchwinger diracFermionW = diracFermionS := by
  ext n α x
  rw [vladimirovSchwinger_eq_zero_eval diracFermionZeroMomentumSpectrumCondition,
      vladimirov_H_zero_diracFermionW]
  rfl

theorem not_diracFermionS_osReflectionPositive :
    ¬ OSReflectionPositive diracStarStructure diracFermionS := by
  intro hrp
  apply not_diracFermionW_positivity
  exact positivity_of_osReflectionPositiveData
    { 𝒮 := diracFermionS
      hermiticity := diracFermionOSHermiticity
      positivity := hrp }
    diracFermionZeroMomentumSpectrumCondition vladimirovSchwinger_diracFermionW.symm

theorem weylFermion_os0_smooth (n : ℕ) (α : Fin n → Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (weylFermionS n α) (orderedEuclidN n) :=
  schwingerFromTube_contDiffOn weylFermionTubeExtension n α

theorem weylFermion_os1_translation :
    OSTranslationInvariant weylFermionS :=
  schwingerFromTube_translation_invariant weylFermionTubeExtension
    weylFermionTubeTranslationInvariant

theorem weylFermion_os1_rotation
    (n : ℕ) (U V : SU2) (x : Fin n → Fin 4 → ℝ)
    (hx : x ∈ orderedEuclidN n) (hRx : euclidRotN n U V x ∈ orderedEuclidN n)
    (α : Fin n → Fin 2) :
    weylFermionS n α (euclidRotN n U V x) =
      ∑ β : Fin n → Fin 2,
        (∏ i : Fin n, leftWeylRep.σ (su2ToSL2C U, su2ToSL2C V) (α i) (β i)) *
          weylFermionS n β x :=
  schwingerFromTube_euclidCovariant leftWeylRep weylFermionW
    weylFermionTubeExtension weylFermionTubeCovariant n U V x hx hRx α

theorem weylFermion_os3_symmetry
    (n : ℕ) (α : Fin n → Fin 2) (x : Fin n → Fin 4 → ℝ) (hx : x ∈ orderedEuclidN n) :
    weylFermionS n α (-(x ∘ Fin.rev)) =
      (-1 : ℂ) ^ (n * (n - 1) / 2) * weylFermionS n (α ∘ Fin.rev) x :=
  schwingerFromTube_weakLocality weylFermionTubeExtension
    weylFermionTubeWeakLocality n α x hx

theorem weylFermion_euclid_spin_statistics {η : ℂ}
    (hsym : ∀ (n : ℕ) (α : Fin n → Fin 2) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n →
      weylFermionS n α (-(x ∘ Fin.rev)) =
        η ^ (n * (n - 1) / 2) * weylFermionS n (α ∘ Fin.rev) x) :
    η = -1 := by
  have hloc : WeakLocality η weylFermionW := by
    rw [vladimirovSchwinger_weakLocality_iff leftWeylRep weylFermionW
        weylFermionZeroMomentumSpectrumCondition weylFermionPoincareCovariant,
        vladimirovSchwinger_weylFermionW]
    exact hsym
  exact weylFermion_spin_statistics_unconditional hloc

theorem diracFermion_os0_smooth (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (diracFermionS n α) (orderedEuclidN n) :=
  schwingerFromTube_contDiffOn diracFermionTubeExtension n α

theorem diracFermion_os1_translation :
    OSTranslationInvariant diracFermionS :=
  schwingerFromTube_translation_invariant diracFermionTubeExtension
    diracFermionTubeTranslationInvariant

theorem diracFermion_os1_rotation
    (n : ℕ) (U V : SU2) (x : Fin n → Fin 4 → ℝ)
    (hx : x ∈ orderedEuclidN n) (hRx : euclidRotN n U V x ∈ orderedEuclidN n)
    (α : Fin n → Fin 2 ⊕ Fin 2) :
    diracFermionS n α (euclidRotN n U V x) =
      ∑ β : Fin n → Fin 2 ⊕ Fin 2,
        (∏ i : Fin n, diracRep.σ (su2ToSL2C U, su2ToSL2C V) (α i) (β i)) *
          diracFermionS n β x :=
  schwingerFromTube_euclidCovariant diracRep diracFermionW
    diracFermionTubeExtension diracFermionTubeCovariant n U V x hx hRx α

theorem diracFermion_os3_symmetry
    (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) (x : Fin n → Fin 4 → ℝ)
    (hx : x ∈ orderedEuclidN n) :
    diracFermionS n α (-(x ∘ Fin.rev)) =
      (-1 : ℂ) ^ (n * (n - 1) / 2) * diracFermionS n (α ∘ Fin.rev) x :=
  schwingerFromTube_weakLocality diracFermionTubeExtension
    diracFermionTubeWeakLocality n α x hx

theorem diracFermion_euclid_spin_statistics {η : ℂ}
    (hsym : ∀ (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n →
      diracFermionS n α (-(x ∘ Fin.rev)) =
        η ^ (n * (n - 1) / 2) * diracFermionS n (α ∘ Fin.rev) x) :
    η = -1 := by
  have hloc : WeakLocality η diracFermionW := by
    rw [vladimirovSchwinger_weakLocality_iff diracRep diracFermionW
        diracFermionZeroMomentumSpectrumCondition diracFermionPoincareCovariant,
        vladimirovSchwinger_diracFermionW]
    exact hsym
  exact diracFermion_spin_statistics_unconditional hloc

theorem diracOSReconstructedWightman_wightman_eq_zero
    {η : ℂ} {𝒮 : SchwingerFamily (Fin 2 ⊕ Fin 2)}
    (P : DiracOSReconstructedWightman η 𝒮)
    (n : ℕ) (hn : 1 ≤ n) (α : Fin n → Fin 2 ⊕ Fin 2)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    P.W n α f = 0 :=
  wightman_diracRep_eq_zero_of_positivity P.W P.spectrum P.poincare P.positivity n hn α f

theorem diracOSReconstructedWightman_eq_vacW
    {η : ℂ} {𝒮 : SchwingerFamily (Fin 2 ⊕ Fin 2)}
    (P : DiracOSReconstructedWightman η 𝒮) (hnorm : OSVacuumNormalized 𝒮)
    (hinj : TubeBoundaryInjective P.E) :
    P.W = vacW :=
  (P.wightman_eq_vacW_iff_twoPoint_wightman_eq_zero hnorm hinj).mpr
    (fun β f => diracOSReconstructedWightman_wightman_eq_zero P 2 (by omega) β f)

@[simp]
theorem measureKallenLehmannTube_neg_comp_rev
    {A : Type*} [MeasurableSpace A] (μ : Measure A) (w E : A → ℝ)
    (z : Fin 2 → Fin 4 → ℂ) :
    measureKallenLehmannTube μ w E (-(z ∘ Fin.rev)) =
      measureKallenLehmannTube μ w E z := by
  unfold measureKallenLehmannTube
  simp_rw [spectralTwoPointTube_neg_comp_rev]

@[simp]
theorem measureKallenLehmannEuclid_neg_comp_rev
    {A : Type*} [MeasurableSpace A] (μ : Measure A) (w E : A → ℝ)
    (x : Fin 2 → Fin 4 → ℝ) :
    measureKallenLehmannEuclid μ w E (-(x ∘ Fin.rev)) =
      measureKallenLehmannEuclid μ w E x := by
  unfold measureKallenLehmannEuclid
  simp_rw [euclidSpectralTwoPoint_neg_comp_rev]

theorem star_measureKallenLehmannTube
    {A : Type*} [MeasurableSpace A] (μ : Measure A) (w E : A → ℝ)
    (z : Fin 2 → Fin 4 → ℂ) :
    star (measureKallenLehmannTube μ w E z) =
      measureKallenLehmannTube μ w E (fun i μ => star (z (Fin.rev i) μ)) := by
  unfold measureKallenLehmannTube
  rw [Complex.star_def, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun a => ?_))
  dsimp
  rw [← Complex.star_def, star_mul', Complex.star_def, Complex.conj_ofReal,
      ← Complex.star_def, star_spectralTwoPointTube]

@[simp]
theorem measureKallenLehmannTube_count_eq_discreteKallenLehmannTube
    (N : ℕ) (w E : Fin N → ℝ) (z : Fin 2 → Fin 4 → ℂ) :
    measureKallenLehmannTube Measure.count w E z =
      discreteKallenLehmannTube N w E z := by
  unfold measureKallenLehmannTube discreteKallenLehmannTube
  exact integral_fintype_count _

@[simp]
theorem measureKallenLehmannEuclid_count_eq_discreteKallenLehmannEuclid
    (N : ℕ) (w E : Fin N → ℝ) (x : Fin 2 → Fin 4 → ℝ) :
    measureKallenLehmannEuclid Measure.count w E x =
      discreteKallenLehmannEuclid N w E x := by
  unfold measureKallenLehmannEuclid discreteKallenLehmannEuclid
  exact integral_fintype_count _

noncomputable def vacSpectralMeasure
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    OSSpectralMeasure (vacOSData R S) (vacOSContraction R S) (Fin 1) :=
  (vacSpectralDecomposition R S).toOSSpectralMeasure

noncomputable def z2FreeSpectralMeasure :
    OSSpectralMeasure z2FreeOSData z2FreeOSContraction (Fin 2) :=
  z2FreeSpectralDecomposition.toOSSpectralMeasure

@[simp]
theorem vacSpectralMeasure_twoPointTubePropagator_eq
    (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (htrans : OSTranslationInvariant (vacOSData R S).𝒮)
    (Ψ Φ : OSHilbert (vacOSData R S))
    (b : Fin 3 → ℝ) (z : Fin 2 → Fin 4 → ℂ) :
    (vacSpectralMeasure R S).twoPointTubePropagator htrans Ψ Φ b z =
      (vacSpectralDecomposition R S).twoPointTubePropagator htrans Ψ Φ b z :=
  (vacSpectralDecomposition R S).toOSSpectralMeasure_twoPointTubePropagator htrans Ψ Φ b z

@[simp]
theorem z2FreeSpectralMeasure_twoPointTubePropagator_eq
    (htrans : OSTranslationInvariant z2FreeOSData.𝒮)
    (Ψ Φ : OSHilbert z2FreeOSData)
    (b : Fin 3 → ℝ) (z : Fin 2 → Fin 4 → ℂ) :
    z2FreeSpectralMeasure.twoPointTubePropagator htrans Ψ Φ b z =
      z2FreeSpectralDecomposition.twoPointTubePropagator htrans Ψ Φ b z :=
  z2FreeSpectralDecomposition.toOSSpectralMeasure_twoPointTubePropagator htrans Ψ Φ b z

theorem vacSpectralMeasure_diag_zero_eq_discreteKallenLehmannTube
    (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (htrans : OSTranslationInvariant (vacOSData R S).𝒮)
    (Ψ : OSHilbert (vacOSData R S)) (z : Fin 2 → Fin 4 → ℂ) :
    (vacSpectralMeasure R S).twoPointTubePropagator htrans Ψ Ψ 0 z =
      discreteKallenLehmannTube 1
        (fun a => ‖(vacSpectralMeasure R S).P a Ψ‖ ^ 2)
        (vacSpectralMeasure R S).E z := by
  rw [(vacSpectralMeasure R S).twoPointTubePropagator_diag_zero_eq_measureKallenLehmannTube]
  exact measureKallenLehmannTube_count_eq_discreteKallenLehmannTube 1 _ _ z

theorem z2FreeSpectralMeasure_diag_zero_eq_discreteKallenLehmannTube
    (htrans : OSTranslationInvariant z2FreeOSData.𝒮)
    (Ψ : OSHilbert z2FreeOSData) (z : Fin 2 → Fin 4 → ℂ) :
    z2FreeSpectralMeasure.twoPointTubePropagator htrans Ψ Ψ 0 z =
      discreteKallenLehmannTube 2
        (fun a => ‖z2FreeSpectralMeasure.P a Ψ‖ ^ 2)
        z2FreeSpectralMeasure.E z := by
  rw [z2FreeSpectralMeasure.twoPointTubePropagator_diag_zero_eq_measureKallenLehmannTube]
  exact measureKallenLehmannTube_count_eq_discreteKallenLehmannTube 2 _ _ z

theorem norm_vacSpectralMeasure_diag_zero_le_norm_sq
    (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (htrans : OSTranslationInvariant (vacOSData R S).𝒮)
    (Ψ : OSHilbert (vacOSData R S)) {z : Fin 2 → Fin 4 → ℂ}
    (hz : z ∈ forward_tube_n 2) :
    ‖(vacSpectralMeasure R S).twoPointTubePropagator htrans Ψ Ψ 0 z‖ ≤ ‖Ψ‖ ^ 2 :=
  (vacSpectralMeasure R S).norm_twoPointTubePropagator_diag_zero_le_norm_sq htrans Ψ hz

theorem norm_z2FreeSpectralMeasure_diag_zero_le_norm_sq
    (htrans : OSTranslationInvariant z2FreeOSData.𝒮)
    (Ψ : OSHilbert z2FreeOSData) {z : Fin 2 → Fin 4 → ℂ}
    (hz : z ∈ forward_tube_n 2) :
    ‖z2FreeSpectralMeasure.twoPointTubePropagator htrans Ψ Ψ 0 z‖ ≤ ‖Ψ‖ ^ 2 :=
  z2FreeSpectralMeasure.norm_twoPointTubePropagator_diag_zero_le_norm_sq htrans Ψ hz

omit [Fintype ι] [DecidableEq ι] in
theorem vacW_forwardConeSpectrumCondition :
    ForwardConeSpectrumCondition (vacW (ι := ι)) :=
  vacZeroMomentumSpectrumCondition.toForwardConeSpectrumCondition

omit [Fintype ι] [DecidableEq ι] in
theorem momentW_forwardConeSpectrumCondition (c : ℕ → ℂ) :
    ForwardConeSpectrumCondition (momentW (ι := ι) c) :=
  (momentZeroMomentumSpectrumCondition c).toForwardConeSpectrumCondition

theorem weylFermionW_forwardConeSpectrumCondition :
    ForwardConeSpectrumCondition weylFermionW :=
  weylFermionZeroMomentumSpectrumCondition.toForwardConeSpectrumCondition

theorem diracFermionW_forwardConeSpectrumCondition :
    ForwardConeSpectrumCondition diracFermionW :=
  diracFermionZeroMomentumSpectrumCondition.toForwardConeSpectrumCondition

theorem z2FreeW_forwardConeSpectrumCondition :
    ForwardConeSpectrumCondition z2FreeW :=
  (momentZeroMomentumSpectrumCondition z2FreeCoeff).toForwardConeSpectrumCondition

noncomputable def vacForwardConeEuclideanTubeBridge
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) :
    ForwardConeOSEuclideanTubeBridge R S η vacS :=
  (vacEuclideanTubeBridge R S η).toForwardConeOSEuclideanTubeBridge

noncomputable def vacForwardConeOSReconstruction
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) :
    ForwardConeOSReconstructedWightman R S η vacS :=
  (vacReconstructedWightmanOfTimeCluster R S η).toForwardConeOSReconstructedWightman

noncomputable def z2FreeForwardConeEuclideanTubeBridge :
    ForwardConeOSEuclideanTubeBridge trivialRep trivialStarStructure 1 z2FreeS :=
  z2FreeEuclideanTubeBridge.toForwardConeOSEuclideanTubeBridge

noncomputable def z2FreeForwardConeOSReconstruction :
    ForwardConeOSReconstructedWightman trivialRep trivialStarStructure 1 z2FreeS :=
  z2FreeOSReconstructedWightman.toForwardConeOSReconstructedWightman

def euclidTwoPointDoubleBase : Fin 2 → Fin 4 → ℝ :=
  fun i μ => if μ = 0 then 2 * ((i.val : ℝ) + 1) else 0

lemma euclidTwoPointDoubleBase_mem_posOrderedEuclidN :
    euclidTwoPointDoubleBase ∈ posOrderedEuclidN 2 := by
  refine ⟨fun i => ?_, fun i hi => ?_⟩
  · dsimp [euclidTwoPointDoubleBase]
    positivity
  · dsimp [euclidTwoPointDoubleBase]
    have hlt : (i.val : ℝ) < ((i.val + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self i.val
    linarith

lemma euclidTwoPointDoubleBase_mem_orderedEuclidN :
    euclidTwoPointDoubleBase ∈ orderedEuclidN 2 :=
  euclidTwoPointDoubleBase_mem_posOrderedEuclidN.2

@[simp]
lemma euclidOrderedBasePoint_two_time_diff :
    euclidOrderedBasePoint 2 1 0 - euclidOrderedBasePoint 2 0 0 = 1 := by
  dsimp [euclidOrderedBasePoint]
  norm_num

@[simp]
lemma euclidTwoPointDoubleBase_time_diff :
    euclidTwoPointDoubleBase 1 0 - euclidTwoPointDoubleBase 0 0 = 2 := by
  dsimp [euclidTwoPointDoubleBase]
  norm_num

theorem euclidSpectralTwoPoint_base_eq (E : ℝ) :
    euclidSpectralTwoPoint E (euclidOrderedBasePoint 2) =
      ((Real.exp (-E) : ℝ) : ℂ) := by
  rw [euclidSpectralTwoPoint_eq_ofReal_exp, euclidOrderedBasePoint_two_time_diff]
  congr 2
  ring

theorem euclidSpectralTwoPoint_doubleBase_eq (E : ℝ) :
    euclidSpectralTwoPoint E euclidTwoPointDoubleBase =
      ((Real.exp (-(2 * E)) : ℝ) : ℂ) := by
  rw [euclidSpectralTwoPoint_eq_ofReal_exp, euclidTwoPointDoubleBase_time_diff]
  congr 2
  ring

theorem euclidSpectralTwoPoint_base_ne_doubleBase {E : ℝ} (hE : E ≠ 0) :
    euclidSpectralTwoPoint E (euclidOrderedBasePoint 2) ≠
      euclidSpectralTwoPoint E euclidTwoPointDoubleBase := by
  rw [euclidSpectralTwoPoint_base_eq, euclidSpectralTwoPoint_doubleBase_eq]
  intro h_eq
  have h_re := Complex.ofReal_injective h_eq
  have h_arg := Real.exp_injective h_re
  apply hE
  linarith

theorem euclidSpectralTwoPoint_nonconstant_on_posOrderedEuclidN {E : ℝ} (hE : E ≠ 0) :
    ∃ x y : Fin 2 → Fin 4 → ℝ,
      x ∈ posOrderedEuclidN 2 ∧
      y ∈ posOrderedEuclidN 2 ∧
      euclidSpectralTwoPoint E x ≠ euclidSpectralTwoPoint E y :=
  ⟨euclidOrderedBasePoint 2, euclidTwoPointDoubleBase,
   euclidOrderedBasePoint_mem_posOrderedEuclidN 2,
   euclidTwoPointDoubleBase_mem_posOrderedEuclidN,
   euclidSpectralTwoPoint_base_ne_doubleBase hE⟩

theorem euclidSpectralTwoPoint_nonconstant_on_orderedEuclidN {E : ℝ} (hE : E ≠ 0) :
    ∃ x y : Fin 2 → Fin 4 → ℝ,
      x ∈ orderedEuclidN 2 ∧
      y ∈ orderedEuclidN 2 ∧
      euclidSpectralTwoPoint E x ≠ euclidSpectralTwoPoint E y :=
  ⟨euclidOrderedBasePoint 2, euclidTwoPointDoubleBase,
   euclidOrderedBasePoint_mem_orderedEuclidN 2,
   euclidTwoPointDoubleBase_mem_orderedEuclidN,
   euclidSpectralTwoPoint_base_ne_doubleBase hE⟩

theorem spectralTwoPointTube_nonconstant_on_forward_tube {E : ℝ} (hE : E ≠ 0) :
    ∃ z w : Fin 2 → Fin 4 → ℂ,
      z ∈ forward_tube_n 2 ∧
      w ∈ forward_tube_n 2 ∧
      spectralTwoPointTube E z ≠ spectralTwoPointTube E w := by
  refine ⟨wickEmbedN 2 (euclidOrderedBasePoint 2),
    wickEmbedN 2 euclidTwoPointDoubleBase,
    wickEmbedN_mem_forward_tube_n 2 (euclidOrderedBasePoint_mem_orderedEuclidN 2),
    wickEmbedN_mem_forward_tube_n 2 euclidTwoPointDoubleBase_mem_orderedEuclidN, ?_⟩
  rw [spectralTwoPointTube_wickEmbedN_eq_euclidSpectralTwoPoint,
      spectralTwoPointTube_wickEmbedN_eq_euclidSpectralTwoPoint]
  exact euclidSpectralTwoPoint_base_ne_doubleBase hE

@[simp]
theorem discreteKallenLehmannEuclid_one_eq
    (w E : Fin 1 → ℝ) (x : Fin 2 → Fin 4 → ℝ) :
    discreteKallenLehmannEuclid 1 w E x =
      (w 0 : ℂ) * euclidSpectralTwoPoint (E 0) x := by
  unfold discreteKallenLehmannEuclid
  exact Fin.sum_univ_one _

@[simp]
theorem discreteKallenLehmannTube_one_eq
    (w E : Fin 1 → ℝ) (z : Fin 2 → Fin 4 → ℂ) :
    discreteKallenLehmannTube 1 w E z =
      (w 0 : ℂ) * spectralTwoPointTube (E 0) z := by
  unfold discreteKallenLehmannTube
  exact Fin.sum_univ_one _

theorem discreteKallenLehmannEuclid_one_nonconstant
    {w E : Fin 1 → ℝ} (hw : w 0 ≠ 0) (hE : E 0 ≠ 0) :
    ∃ x y : Fin 2 → Fin 4 → ℝ,
      x ∈ posOrderedEuclidN 2 ∧
      y ∈ posOrderedEuclidN 2 ∧
      discreteKallenLehmannEuclid 1 w E x ≠
        discreteKallenLehmannEuclid 1 w E y := by
  refine ⟨euclidOrderedBasePoint 2, euclidTwoPointDoubleBase,
    euclidOrderedBasePoint_mem_posOrderedEuclidN 2,
    euclidTwoPointDoubleBase_mem_posOrderedEuclidN, ?_⟩
  rw [discreteKallenLehmannEuclid_one_eq, discreteKallenLehmannEuclid_one_eq]
  have hwC : (w 0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw
  exact mul_right_injective₀ hwC |>.ne (euclidSpectralTwoPoint_base_ne_doubleBase hE)

theorem discreteKallenLehmannTube_one_nonconstant
    {w E : Fin 1 → ℝ} (hw : w 0 ≠ 0) (hE : E 0 ≠ 0) :
    ∃ z₁ z₂ : Fin 2 → Fin 4 → ℂ,
      z₁ ∈ forward_tube_n 2 ∧
      z₂ ∈ forward_tube_n 2 ∧
      discreteKallenLehmannTube 1 w E z₁ ≠
        discreteKallenLehmannTube 1 w E z₂ := by
  rcases spectralTwoPointTube_nonconstant_on_forward_tube hE with
    ⟨z₁, z₂, hz₁, hz₂, hne⟩
  refine ⟨z₁, z₂, hz₁, hz₂, ?_⟩
  rw [discreteKallenLehmannTube_one_eq, discreteKallenLehmannTube_one_eq]
  have hwC : (w 0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw
  exact mul_right_injective₀ hwC |>.ne hne

theorem singleMode_positiveEnergy_kallenLehmann_properties
    {w₀ E₀ : ℝ} (hw₀ : 0 < w₀) (hE₀ : 0 < E₀) :
    (∀ z ∈ forward_tube_n 2,
      ‖discreteKallenLehmannTube 1 (fun _ => w₀) (fun _ => E₀) z‖ ≤ w₀) ∧
    (∀ (m : ℕ) (c : Fin m → ℂ) (x : Fin m → Fin 1 → Fin 4 → ℝ),
      0 ≤ RCLike.re (∑ j : Fin m, ∑ k : Fin m,
        star (c j) * c k *
          discreteKallenLehmannEuclid 1 (fun _ => w₀) (fun _ => E₀)
            (osConcatPoint 1 1 (x j) (x k)))) ∧
    (∀ x y : Fin 1 → Fin 4 → ℝ,
      Tendsto
        (fun τ : ℝ =>
          discreteKallenLehmannEuclid 1 (fun _ => w₀) (fun _ => E₀)
            (osConcatPoint 1 1 x (fun i => y i + euclidTimeVec τ)))
        atTop (𝓝 0)) ∧
    (∃ x y : Fin 2 → Fin 4 → ℝ,
      x ∈ posOrderedEuclidN 2 ∧
      y ∈ posOrderedEuclidN 2 ∧
      discreteKallenLehmannEuclid 1 (fun _ => w₀) (fun _ => E₀) x ≠
        discreteKallenLehmannEuclid 1 (fun _ => w₀) (fun _ => E₀) y) ∧
    (∃ z₁ z₂ : Fin 2 → Fin 4 → ℂ,
      z₁ ∈ forward_tube_n 2 ∧
      z₂ ∈ forward_tube_n 2 ∧
      discreteKallenLehmannTube 1 (fun _ => w₀) (fun _ => E₀) z₁ ≠
        discreteKallenLehmannTube 1 (fun _ => w₀) (fun _ => E₀) z₂) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [discreteKallenLehmannTube_one_eq]
    exact norm_measureKallenLehmannTube_integrand_le
      (w := fun _ : Fin 1 => w₀) (E := fun _ : Fin 1 => E₀) (a := 0)
      (le_of_lt hw₀) (le_of_lt hE₀) hz
  · intro m c x
    exact discreteKallenLehmannEuclid_reflectionPositive
      (fun _ => le_of_lt hw₀) (fun _ => E₀) m c x
  · intro x y
    exact tendsto_discreteKallenLehmannEuclid_timeShift_atTop_zero
      (fun _ => w₀) (fun _ => hE₀) x y
  · exact discreteKallenLehmannEuclid_one_nonconstant
      (ne_of_gt hw₀) (ne_of_gt hE₀)
  · exact discreteKallenLehmannTube_one_nonconstant
      (ne_of_gt hw₀) (ne_of_gt hE₀)

def alternatingMomentum (n : ℕ) (q : Fin 4 → ℝ) : Fin n → Fin 4 → ℝ :=
  fun i => if i.val % 2 = 0 then q else -q

@[simp]
lemma alternatingMomentum_apply (n : ℕ) (q : Fin 4 → ℝ) (i : Fin n) :
    alternatingMomentum n q i = if i.val % 2 = 0 then q else -q := rfl

@[simp]
lemma alternatingMomentum_two_eq_twoPointMomentum (q : Fin 4 → ℝ) :
    alternatingMomentum 2 q = twoPointMomentum q := by
  ext i μ
  fin_cases i <;> rfl

lemma sum_range_alternating (m : ℕ) (q : Fin 4 → ℝ) :
    (∑ j ∈ Finset.range m, if j % 2 = 0 then q else -q) =
      if m % 2 = 0 then 0 else q := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.mod_two_eq_zero_or_one m with hm0 | hm1
    · have hm1' : (m + 1) % 2 ≠ 0 := by omega
      simp [hm0, hm1']
    · have hm_ne : m % 2 ≠ 0 := by omega
      have hm1' : (m + 1) % 2 = 0 := by omega
      simp [hm_ne, hm1']

lemma sum_alternatingMomentum_of_even (n : ℕ) (hn : n % 2 = 0) (q : Fin 4 → ℝ) :
    ∑ i : Fin n, alternatingMomentum n q i = 0 := by
  change (∑ i : Fin n, if i.val % 2 = 0 then q else -q) = 0
  rw [Fin.sum_univ_eq_sum_range (fun j => if j % 2 = 0 then q else -q) n,
      sum_range_alternating n q, if_pos hn]

lemma partial_sum_alternatingMomentum (n : ℕ) (q : Fin 4 → ℝ) (k : Fin n) :
    (∑ i ∈ Finset.univ.filter (· ≤ k), alternatingMomentum n q i) =
      if k.val % 2 = 0 then q else 0 := by
  have h_eq := partial_sum_p_eq n (alternatingMomentum n q) k
    (fun j => if j % 2 = 0 then q else -q) (fun _ => rfl)
  change partial_sum_p n (alternatingMomentum n q) k = _
  rw [h_eq, sum_range_alternating (k.val + 1) q]
  rcases Nat.mod_two_eq_zero_or_one k.val with hk0 | hk1
  · have hk1 : (k.val + 1) % 2 ≠ 0 := by omega
    rw [if_neg hk1, if_pos hk0]
  · have hk_ne : k.val % 2 ≠ 0 := by omega
    have hk1' : (k.val + 1) % 2 = 0 := by omega
    rw [if_pos hk1', if_neg hk_ne]

theorem alternatingMomentum_mem_forwardConeSpectralRegion
    (n : ℕ) (hn : n % 2 = 0) {q : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone) :
    alternatingMomentum n q ∈ forwardConeSpectralRegion n := by
  refine ⟨sum_alternatingMomentum_of_even n hn q, fun k => ?_⟩
  rw [partial_sum_alternatingMomentum]
  split_ifs
  · exact hq
  · exact zero_mem_closure_forward_light_cone

noncomputable def fourMomentumSpectralFamily (q : Fin 4 → ℝ)
    (hq : q ∈ closure forward_light_cone) :
    ForwardConeSpectralFamily Unit where
  m n := if n % 2 = 0 then 1 else 0
  c n _ _ := if n % 2 = 0 then 1 else 0
  p n _ _ := if n % 2 = 0 then alternatingMomentum n q else 0
  mem_forwardCone n _ k := by
    by_cases hn : n % 2 = 0
    · rw [if_pos hn]
      exact alternatingMomentum_mem_forwardConeSpectralRegion n hn hq
    · exact False.elim (Fin.elim0 (Fin.cast (if_neg hn) k))

noncomputable def fourMomentumW (q : Fin 4 → ℝ) : WightmanFamily Unit :=
  fun n _ => if n % 2 = 0 then minkowskiFourierEvalTD n (alternatingMomentum n q) else 0

@[simp]
theorem fourMomentumW_apply (q : Fin 4 → ℝ) (n : ℕ) (α : Fin n → Unit)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    fourMomentumW q n α f =
      if n % 2 = 0 then minkowskiFourier f (alternatingMomentum n q) else 0 := by
  dsimp [fourMomentumW]
  split_ifs
  · exact minkowskiFourierEvalTD_apply n (alternatingMomentum n q) f
  · rfl

noncomputable def fourMomentumH (q : Fin 4 → ℝ)
    (n : ℕ) (_α : Fin n → Unit) (z : Fin n → Fin 4 → ℂ) : ℂ :=
  if n % 2 = 0 then vladimirov_kernel n z (alternatingMomentum n q) else 0

@[simp]
theorem fourMomentumSpectralFamily_toWightmanFamily
    {q : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone) :
    (fourMomentumSpectralFamily q hq).toWightmanFamily = fourMomentumW q := by
  ext n α f
  rw [ForwardConeSpectralFamily.toWightmanFamily_apply, fourMomentumW_apply]
  unfold fourMomentumSpectralFamily
  by_cases hn : n % 2 = 0
  · simp [hn]
  · simp [hn]

@[simp]
theorem fourMomentumSpectralFamily_H
    {q : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone)
    (n : ℕ) (α : Fin n → Unit) (z : Fin n → Fin 4 → ℂ) :
    (fourMomentumSpectralFamily q hq).H n α z = fourMomentumH q n α z := by
  unfold ForwardConeSpectralFamily.H fourMomentumSpectralFamily fourMomentumH
  by_cases hn : n % 2 = 0
  · simp [hn]
  · simp [hn]

noncomputable def fourMomentumTubeExtension (q : Fin 4 → ℝ) :
    TubeExtension (fourMomentumW q) where
  H := fourMomentumH q
  analytic n α := by
    unfold fourMomentumH
    by_cases hn : n % 2 = 0
    · simp only [if_pos hn]
      exact vladimirov_kernel_analyticOn n (alternatingMomentum n q) (forward_tube_n n)
    · simp only [if_neg hn]
      exact analyticOn_const
  boundary n α f v _hv := by
    rw [fourMomentumW_apply]
    unfold fourMomentumH
    by_cases hn : n % 2 = 0
    · simp only [if_pos hn]
      exact tendsto_integral_vladimirov_kernel_line_mul_f n f (alternatingMomentum n q) v
    · simp only [if_neg hn, zero_mul, integral_zero]
      exact tendsto_const_nhds

@[simp]
theorem fourMomentumTubeExtension_H (q : Fin 4 → ℝ) :
    (fourMomentumTubeExtension q).H = fourMomentumH q := rfl

noncomputable def fourMomentumS (q : Fin 4 → ℝ) : SchwingerFamily Unit :=
  schwingerFromTube (fourMomentumTubeExtension q)

@[simp]
theorem fourMomentumS_apply (q : Fin 4 → ℝ) (n : ℕ) (α : Fin n → Unit)
    (x : Fin n → Fin 4 → ℝ) :
    fourMomentumS q n α x = fourMomentumH q n α (wickEmbedN n x) := rfl

@[simp]
theorem fourMomentumH_zero (q : Fin 4 → ℝ) (α : Fin 0 → Unit) (z : Fin 0 → Fin 4 → ℂ) :
    fourMomentumH q 0 α z = 1 := by
  unfold fourMomentumH vladimirov_kernel
  simp

@[simp]
theorem fourMomentumS_zero (q : Fin 4 → ℝ) (α : Fin 0 → Unit) (x : Fin 0 → Fin 4 → ℝ) :
    fourMomentumS q 0 α x = 1 :=
  fourMomentumH_zero q α (wickEmbedN 0 x)

theorem fourMomentumS_vacuumNormalized (q : Fin 4 → ℝ) :
    OSVacuumNormalized (fourMomentumS q) :=
  fourMomentumS_zero q Fin.elim0 (euclidOrderedBasePoint 0)

@[simp]
theorem fourMomentumH_two (q : Fin 4 → ℝ) (α : Fin 2 → Unit) (z : Fin 2 → Fin 4 → ℂ) :
    fourMomentumH q 2 α z = vladimirov_kernel 2 z (twoPointMomentum q) := by
  unfold fourMomentumH
  simp

@[simp]
theorem fourMomentumH_two_euclidTimeVec (E : ℝ) (α : Fin 2 → Unit) (z : Fin 2 → Fin 4 → ℂ) :
    fourMomentumH (euclidTimeVec E) 2 α z = spectralTwoPointTube E z := by
  rw [fourMomentumH_two, vladimirov_kernel_twoPointMomentum_euclidTimeVec_eq_spectralTwoPointTube]

@[simp]
theorem fourMomentumS_two_euclidTimeVec (E : ℝ) (α : Fin 2 → Unit) (x : Fin 2 → Fin 4 → ℝ) :
    fourMomentumS (euclidTimeVec E) 2 α x = euclidSpectralTwoPoint E x := by
  rw [fourMomentumS_apply, fourMomentumH_two_euclidTimeVec,
      spectralTwoPointTube_wickEmbedN_eq_euclidSpectralTwoPoint]

@[simp]
theorem fourMomentumW_two_apply (q : Fin 4 → ℝ) (α : Fin 2 → Unit)
    (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ) :
    fourMomentumW q 2 α f = minkowskiFourier f (twoPointMomentum q) := by
  rw [fourMomentumW_apply, if_pos rfl, alternatingMomentum_two_eq_twoPointMomentum]

theorem fourMomentumTubeTranslationInvariant (q : Fin 4 → ℝ) :
    TubeTranslationInvariant (fourMomentumTubeExtension q) := by
  intro n α z a _hz
  change fourMomentumH q n α (fun i => z i + a) = fourMomentumH q n α z
  unfold fourMomentumH
  by_cases hn : n % 2 = 0
  · simp only [if_pos hn]
    exact vladimirov_kernel_add_const_of_sum_eq_zero n
      (sum_alternatingMomentum_of_even n hn q) z a
  · simp [hn]

theorem fourMomentumOSTranslationInvariant (q : Fin 4 → ℝ) :
    OSTranslationInvariant (fourMomentumS q) :=
  schwingerFromTube_translation_invariant (fourMomentumTubeExtension q)
    (fourMomentumTubeTranslationInvariant q)

theorem fourMomentumW_forwardConeSpectrumCondition
    {q : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone) :
    ForwardConeSpectrumCondition (fourMomentumW q) := by
  rw [← fourMomentumSpectralFamily_toWightmanFamily hq]
  exact (fourMomentumSpectralFamily q hq).forwardConeSpectrumCondition

theorem norm_fourMomentumH_le_one {q : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone)
    (n : ℕ) (α : Fin n → Unit) {z : Fin n → Fin 4 → ℂ} (hz : z ∈ forward_tube_n n) :
    ‖fourMomentumH q n α z‖ ≤ 1 := by
  unfold fourMomentumH
  by_cases hn : n % 2 = 0
  · rw [if_pos hn]
    exact vladimirov_kernel_norm_le_one_of_forwardConeSpectralRegion n
      (alternatingMomentum n q) (alternatingMomentum_mem_forwardConeSpectralRegion n hn hq) z hz
  · rw [if_neg hn, norm_zero]
    exact zero_le_one

lemma twoPointMomentum_ne_zero_of_ne_zero {q : Fin 4 → ℝ} (hq : q ≠ 0) :
    twoPointMomentum q ≠ 0 := by
  intro h
  apply hq
  have h0 := congr_fun h 0
  simpa using h0

lemma vladimirov_psi_schwartz_eval_of_norm_le
    {n : ℕ} {R : ℝ} (hR : 0 < R) (z : Fin n → Fin 4 → ℂ)
    {p : Fin n → Fin 4 → ℝ} (hp : ‖p‖ ≤ R) :
    vladimirov_psi_schwartz n R hR z p = vladimirov_kernel n z p := by
  change vladimirov_psi n R hR z p = vladimirov_kernel n z p
  dsimp [vladimirov_psi]
  have h_bump : (vladimirovCutoffBump n R hR p : ℝ) = 1 := by
    apply (vladimirovCutoffBump n R hR).one_of_mem_closedBall
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact hp
  rw [h_bump, Complex.ofReal_one, one_mul]

theorem not_zeroMomentumSpectrumCondition_fourMomentumW {q : Fin 4 → ℝ} (hq : q ≠ 0) :
    ¬ ZeroMomentumSpectrumCondition (fourMomentumW q) := by
  intro hspec
  let p₀ : Fin 2 → Fin 4 → ℝ := twoPointMomentum q
  let R : ℝ := ‖p₀‖ + 1
  have hR : 0 < R := by positivity
  let f₀ : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ :=
    invMinkowskiFourierCLM 2 (vladimirov_psi_schwartz 2 R hR 0)
  have h_zero : ∀ g : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ,
      minkowskiFourier g 0 = 0 → fourMomentumW q 2 default g = 0 :=
    hspec 2 default
  have h_int_eq := W_n_eq_integral_of_zero_fourier (fourMomentumW q) 2 default h_zero
  have h0_le_R : ‖(0 : Fin 2 → Fin 4 → ℝ)‖ ≤ R := by
    rw [norm_zero]
    exact le_of_lt hR
  have hp₀_le_R : ‖p₀‖ ≤ R := by
    dsimp [R]
    linarith
  have hf₀_int : (∫ x, f₀ x) = 1 := by
    rw [← minkowskiFourier_eval_zero_n]
    dsimp [f₀]
    rw [minkowskiFourier_invMinkowskiFourierCLM_all,
        vladimirov_psi_schwartz_eval_of_norm_le hR 0 h0_le_R]
    simp [vladimirov_kernel, minkowskiInnerC]
  have hf₀_p₀ : minkowskiFourier f₀ p₀ = 1 := by
    dsimp [f₀]
    rw [minkowskiFourier_invMinkowskiFourierCLM_all,
        vladimirov_psi_schwartz_eval_of_norm_le hR 0 hp₀_le_R]
    simp [vladimirov_kernel, minkowskiInnerC]
  have hW_f₀ : fourMomentumW q 2 default f₀ = 1 := by
    rw [fourMomentumW_two_apply]
    exact hf₀_p₀
  have hH0 : vladimirov_H (fourMomentumW q) 2 default 0 = 1 := by
    have h1 := h_int_eq f₀
    rw [hW_f₀, hf₀_int, mul_one] at h1
    exact h1.symm
  have h_all : ∀ g : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ,
      minkowskiFourier g p₀ = minkowskiFourier g 0 := by
    intro g
    have h1 := h_int_eq g
    rw [fourMomentumW_two_apply, hH0, one_mul, ← minkowskiFourier_eval_zero_n] at h1
    exact h1
  obtain ⟨μ, hμ⟩ : ∃ μ : Fin 4, q μ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hq (funext hc)
  let sμ : ℝ := if μ = 0 then 1 else -1
  let z₁ : Fin 2 → Fin 4 → ℂ :=
    fun i ν => if i = 0 ∧ ν = μ then ((-1 / (sμ * q μ) : ℝ) : ℂ) else 0
  let f₁ : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ :=
    invMinkowskiFourierCLM 2 (vladimirov_psi_schwartz 2 R hR z₁)
  have hf₁_zero : minkowskiFourier f₁ 0 = 1 := by
    dsimp [f₁]
    rw [minkowskiFourier_invMinkowskiFourierCLM_all,
        vladimirov_psi_schwartz_eval_of_norm_le hR z₁ h0_le_R]
    simp [vladimirov_kernel, minkowskiInnerC]
  have hf₁_p₀ : minkowskiFourier f₁ p₀ =
      vladimirov_kernel 2 z₁ p₀ := by
    dsimp [f₁]
    rw [minkowskiFourier_invMinkowskiFourierCLM_all,
        vladimirov_psi_schwartz_eval_of_norm_le hR z₁ hp₀_le_R]
  have h_ker_eq_one : vladimirov_kernel 2 z₁ p₀ = 1 := by
    rw [← hf₁_p₀, h_all f₁, hf₁_zero]
  have h_ker_val : vladimirov_kernel 2 z₁ p₀ =
      Complex.exp (((1 : ℝ) : ℂ) * Complex.I) := by
    unfold vladimirov_kernel
    congr 1
    rw [Fin.sum_univ_two]
    have h_z1_1 : z₁ 1 = 0 := by
      ext ν
      dsimp [z₁]
    have h_inner1 : minkowskiInnerC (fun ν => (p₀ 1 ν : ℂ)) (z₁ 1) = 0 := by
      rw [h_z1_1]
      simp [minkowskiInnerC]
    rw [h_inner1, add_zero]
    have hp₀_0 : ∀ ν : Fin 4, p₀ 0 ν = q ν := fun _ => rfl
    have h_inner0 : minkowskiInnerC (fun ν => (p₀ 0 ν : ℂ)) (z₁ 0) = -1 := by
      dsimp [minkowskiInnerC, z₁, sμ]
      simp_rw [hp₀_0]
      fin_cases μ
      · dsimp
        push_cast
        have hqμ : (q 0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ
        field_simp [hqμ]
        ring
      · dsimp
        push_cast
        have hqμ : (q 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ
        field_simp [hqμ]
        ring
      · dsimp
        push_cast
        have hqμ : (q 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ
        field_simp [hqμ]
        ring
      · dsimp
        push_cast
        have hqμ : (q 3 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ
        field_simp [hqμ]
        ring
    rw [h_inner0]
    push_cast
    ring
  rw [h_ker_val] at h_ker_eq_one
  have h_im := congrArg Complex.im h_ker_eq_one
  rw [Complex.exp_mul_I, Complex.add_im, Complex.cos_ofReal_im,
      Complex.mul_I_im, Complex.sin_ofReal_re, zero_add, Complex.one_im] at h_im
  have h_sin_pos : 0 < Real.sin 1 :=
    Real.sin_pos_of_pos_of_lt_pi zero_lt_one (by linarith [Real.pi_gt_three])
  linarith

theorem exists_wightman_forwardConeSpectrumCondition_not_zeroMomentumSpectrumCondition :
    ∃ W : WightmanFamily Unit,
      ForwardConeSpectrumCondition W ∧ ¬ ZeroMomentumSpectrumCondition W := by
  refine ⟨fourMomentumW (euclidTimeVec 1),
    fourMomentumW_forwardConeSpectrumCondition
      (euclidTimeVec_mem_closure_forward_light_cone zero_le_one),
    not_zeroMomentumSpectrumCondition_fourMomentumW ?_⟩
  intro h
  have h0 := congr_fun h 0
  simp [euclidTimeVec] at h0

lemma vladimirov_kernel_two_wickEmbedN_twoPointMomentum
    (q : Fin 4 → ℝ) (x : Fin 2 → Fin 4 → ℝ) :
    vladimirov_kernel 2 (wickEmbedN 2 x) (twoPointMomentum q) =
      ((Real.exp (-(x 1 0 - x 0 0) * q 0) : ℝ) : ℂ) *
        Complex.exp (- Complex.I *
          (((x 1 1 - x 0 1) * q 1 +
            (x 1 2 - x 0 2) * q 2 +
            (x 1 3 - x 0 3) * q 3 : ℝ) : ℂ)) := by
  unfold vladimirov_kernel
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  rw [Fin.sum_univ_two]
  dsimp [twoPointMomentum, wickEmbedN, wickEmbed, minkowskiInnerC]
  push_cast
  linear_combination
    (-(q 0 : ℂ) * (x 0 0 : ℂ) + (q 0 : ℂ) * (x 1 0 : ℂ)) * Complex.I_sq

theorem fourMomentumS_two_eq (q : Fin 4 → ℝ) (α : Fin 2 → Unit) (x : Fin 2 → Fin 4 → ℝ) :
    fourMomentumS q 2 α x =
      ((Real.exp (-(x 1 0 - x 0 0) * q 0) : ℝ) : ℂ) *
        Complex.exp (- Complex.I *
          (((x 1 1 - x 0 1) * q 1 +
            (x 1 2 - x 0 2) * q 2 +
            (x 1 3 - x 0 3) * q 3 : ℝ) : ℂ)) := by
  rw [fourMomentumS_apply, fourMomentumH_two]
  exact vladimirov_kernel_two_wickEmbedN_twoPointMomentum q x

theorem fourMomentumS_two_base_eq (q : Fin 4 → ℝ) (α : Fin 2 → Unit) :
    fourMomentumS q 2 α (euclidOrderedBasePoint 2) =
      ((Real.exp (-q 0) : ℝ) : ℂ) := by
  rw [fourMomentumS_two_eq]
  have h_time : euclidOrderedBasePoint 2 1 0 - euclidOrderedBasePoint 2 0 0 = 1 :=
    euclidOrderedBasePoint_two_time_diff
  have h_s1 : euclidOrderedBasePoint 2 1 1 - euclidOrderedBasePoint 2 0 1 = 0 := by
    simp [euclidOrderedBasePoint]
  have h_s2 : euclidOrderedBasePoint 2 1 2 - euclidOrderedBasePoint 2 0 2 = 0 := by
    simp [euclidOrderedBasePoint]
  have h_s3 : euclidOrderedBasePoint 2 1 3 - euclidOrderedBasePoint 2 0 3 = 0 := by
    simp [euclidOrderedBasePoint]
  rw [h_time, h_s1, h_s2, h_s3]
  simp

theorem fourMomentumS_two_doubleBase_eq (q : Fin 4 → ℝ) (α : Fin 2 → Unit) :
    fourMomentumS q 2 α euclidTwoPointDoubleBase =
      ((Real.exp (-(2 * q 0)) : ℝ) : ℂ) := by
  rw [fourMomentumS_two_eq]
  have h_time : euclidTwoPointDoubleBase 1 0 - euclidTwoPointDoubleBase 0 0 = 2 :=
    euclidTwoPointDoubleBase_time_diff
  have h_s1 : euclidTwoPointDoubleBase 1 1 - euclidTwoPointDoubleBase 0 1 = 0 := by
    simp [euclidTwoPointDoubleBase]
  have h_s2 : euclidTwoPointDoubleBase 1 2 - euclidTwoPointDoubleBase 0 2 = 0 := by
    simp [euclidTwoPointDoubleBase]
  have h_s3 : euclidTwoPointDoubleBase 1 3 - euclidTwoPointDoubleBase 0 3 = 0 := by
    simp [euclidTwoPointDoubleBase]
  rw [h_time, h_s1, h_s2, h_s3]
  simp

theorem fourMomentumS_two_base_ne_doubleBase {q : Fin 4 → ℝ} (hq0 : q 0 ≠ 0)
    (α : Fin 2 → Unit) :
    fourMomentumS q 2 α (euclidOrderedBasePoint 2) ≠
      fourMomentumS q 2 α euclidTwoPointDoubleBase := by
  rw [fourMomentumS_two_base_eq, fourMomentumS_two_doubleBase_eq]
  intro h_eq
  have h_re := Complex.ofReal_injective h_eq
  have h_arg := Real.exp_injective h_re
  apply hq0
  linarith

noncomputable def euclidTwoPointSpatialShift (s : ℝ) : Fin 2 → Fin 4 → ℝ :=
  fun i μ =>
    if μ = 0 then (i.val : ℝ) + 1
    else if i = 1 ∧ μ = 1 then s
    else 0

lemma euclidTwoPointSpatialShift_mem_posOrderedEuclidN (s : ℝ) :
    euclidTwoPointSpatialShift s ∈ posOrderedEuclidN 2 := by
  refine ⟨fun i => ?_, fun i hi => ?_⟩
  · dsimp [euclidTwoPointSpatialShift]
    positivity
  · dsimp [euclidTwoPointSpatialShift]
    have hlt : (i.val : ℝ) < ((i.val + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_succ_self i.val
    linarith

lemma euclidTwoPointSpatialShift_mem_orderedEuclidN (s : ℝ) :
    euclidTwoPointSpatialShift s ∈ orderedEuclidN 2 :=
  (euclidTwoPointSpatialShift_mem_posOrderedEuclidN s).2

theorem fourMomentumS_two_spatialShift_eq (q : Fin 4 → ℝ) (s : ℝ) (α : Fin 2 → Unit) :
    fourMomentumS q 2 α (euclidTwoPointSpatialShift s) =
      ((Real.exp (-q 0) : ℝ) : ℂ) *
        Complex.exp (- Complex.I * ((s * q 1 : ℝ) : ℂ)) := by
  rw [fourMomentumS_two_eq]
  have h_time :
      euclidTwoPointSpatialShift s 1 0 - euclidTwoPointSpatialShift s 0 0 = 1 := by
    dsimp [euclidTwoPointSpatialShift]
    norm_num
  have h_s1 :
      euclidTwoPointSpatialShift s 1 1 - euclidTwoPointSpatialShift s 0 1 = s := by
    dsimp [euclidTwoPointSpatialShift]
    norm_num
  have h_s2 :
      euclidTwoPointSpatialShift s 1 2 - euclidTwoPointSpatialShift s 0 2 = 0 := by
    dsimp [euclidTwoPointSpatialShift]
    norm_num
  have h_s3 :
      euclidTwoPointSpatialShift s 1 3 - euclidTwoPointSpatialShift s 0 3 = 0 := by
    dsimp [euclidTwoPointSpatialShift]
    norm_num
  rw [h_time, h_s1, h_s2, h_s3]
  simp

theorem fourMomentumS_two_base_ne_spatialShift {q : Fin 4 → ℝ} (hq1 : q 1 ≠ 0)
    (α : Fin 2 → Unit) :
    fourMomentumS q 2 α (euclidOrderedBasePoint 2) ≠
      fourMomentumS q 2 α (euclidTwoPointSpatialShift (Real.pi / q 1)) := by
  rw [fourMomentumS_two_base_eq, fourMomentumS_two_spatialShift_eq]
  have h_prod : Real.pi / q 1 * q 1 = Real.pi := div_mul_cancel₀ Real.pi hq1
  rw [h_prod]
  have h_exp_pi : Complex.exp (- Complex.I * (Real.pi : ℂ)) = -1 := by
    have h_eq : - Complex.I * (Real.pi : ℂ) = -((Real.pi : ℂ) * Complex.I) := by ring
    rw [h_eq, Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]
  rw [h_exp_pi, mul_neg_one]
  intro h_eq
  have h_re := congrArg Complex.re h_eq
  simp only [Complex.ofReal_re, Complex.neg_re] at h_re
  have h_pos : 0 < Real.exp (-q 0) := Real.exp_pos (-q 0)
  linarith

def sampleFourMomentum : Fin 4 → ℝ := ![2, 1, 0, 0]

lemma sampleFourMomentum_zero : sampleFourMomentum 0 = 2 := rfl

lemma sampleFourMomentum_one : sampleFourMomentum 1 = 1 := rfl

lemma sampleFourMomentum_zero_ne_zero : sampleFourMomentum 0 ≠ 0 := by
  rw [sampleFourMomentum_zero]
  norm_num

lemma sampleFourMomentum_one_ne_zero : sampleFourMomentum 1 ≠ 0 := by
  rw [sampleFourMomentum_one]
  norm_num

lemma sampleFourMomentum_mem_forward_light_cone :
    sampleFourMomentum ∈ forward_light_cone := by
  refine ⟨?_, ?_⟩
  · rw [sampleFourMomentum_zero]
    norm_num
  · rw [minkowskiInner_explicit]
    dsimp [sampleFourMomentum]
    norm_num

lemma sampleFourMomentum_mem_closure_forward_light_cone :
    sampleFourMomentum ∈ closure forward_light_cone :=
  subset_closure sampleFourMomentum_mem_forward_light_cone

lemma sampleFourMomentum_ne_zero : sampleFourMomentum ≠ 0 := by
  intro h
  exact sampleFourMomentum_zero_ne_zero (congr_fun h 0)

theorem sampleFourMomentum_twoPoint_4d_properties :
    ForwardConeSpectrumCondition (fourMomentumW sampleFourMomentum) ∧
    ¬ ZeroMomentumSpectrumCondition (fourMomentumW sampleFourMomentum) ∧
    (∀ (n : ℕ) (α : Fin n → Unit) (z : Fin n → Fin 4 → ℂ),
      z ∈ forward_tube_n n → ‖fourMomentumH sampleFourMomentum n α z‖ ≤ 1) ∧
    (∃ x y : Fin 2 → Fin 4 → ℝ,
      x ∈ posOrderedEuclidN 2 ∧
      y ∈ posOrderedEuclidN 2 ∧
      (∀ i : Fin 2, ∀ j : Fin 3, x i j.succ = y i j.succ) ∧
      fourMomentumS sampleFourMomentum 2 default x ≠
        fourMomentumS sampleFourMomentum 2 default y) ∧
    (∃ x y : Fin 2 → Fin 4 → ℝ,
      x ∈ posOrderedEuclidN 2 ∧
      y ∈ posOrderedEuclidN 2 ∧
      (∀ i : Fin 2, x i 0 = y i 0) ∧
      fourMomentumS sampleFourMomentum 2 default x ≠
        fourMomentumS sampleFourMomentum 2 default y) := by
  refine ⟨fourMomentumW_forwardConeSpectrumCondition
      sampleFourMomentum_mem_closure_forward_light_cone,
    not_zeroMomentumSpectrumCondition_fourMomentumW sampleFourMomentum_ne_zero,
    fun n α z hz => norm_fourMomentumH_le_one
      sampleFourMomentum_mem_closure_forward_light_cone n α hz,
    ?_, ?_⟩
  · refine ⟨euclidOrderedBasePoint 2, euclidTwoPointDoubleBase,
      euclidOrderedBasePoint_mem_posOrderedEuclidN 2,
      euclidTwoPointDoubleBase_mem_posOrderedEuclidN,
      fun i j => ?_,
      fourMomentumS_two_base_ne_doubleBase sampleFourMomentum_zero_ne_zero default⟩
    simp [euclidOrderedBasePoint, euclidTwoPointDoubleBase, Fin.succ_ne_zero]
  · refine ⟨euclidOrderedBasePoint 2,
      euclidTwoPointSpatialShift (Real.pi / sampleFourMomentum 1),
      euclidOrderedBasePoint_mem_posOrderedEuclidN 2,
      euclidTwoPointSpatialShift_mem_posOrderedEuclidN _,
      fun i => rfl,
      fourMomentumS_two_base_ne_spatialShift sampleFourMomentum_one_ne_zero default⟩

theorem fourMomentumS_euclidTimeVec_twoPoint_reflectionPositive
    (E : ℝ) (m : ℕ) (c : Fin m → ℂ) (x : Fin m → Fin 1 → Fin 4 → ℝ) :
    0 ≤ RCLike.re (∑ j : Fin m, ∑ k : Fin m,
      star (c j) * c k *
        fourMomentumS (euclidTimeVec E) 2 default (osConcatPoint 1 1 (x j) (x k))) := by
  simp_rw [fourMomentumS_two_euclidTimeVec]
  exact euclidSpectralTwoPoint_reflectionPositive E m c x

theorem tendsto_fourMomentumS_euclidTimeVec_twoPoint_timeShift_atTop_zero
    {E : ℝ} (hE : 0 < E) (x y : Fin 1 → Fin 4 → ℝ) :
    Tendsto
      (fun τ : ℝ =>
        fourMomentumS (euclidTimeVec E) 2 default
          (osConcatPoint 1 1 x (fun i => y i + euclidTimeVec τ)))
      atTop (𝓝 0) := by
  simp_rw [fourMomentumS_two_euclidTimeVec]
  exact tendsto_euclidSpectralTwoPoint_timeShift_atTop_zero hE x y

@[simp]
lemma alternatingMomentum_neg (n : ℕ) (q : Fin 4 → ℝ) :
    alternatingMomentum n (-q) = -alternatingMomentum n q := by
  ext i μ
  dsimp [alternatingMomentum]
  split_ifs <;> simp

lemma alternatingMomentum_castAdd_rev (j k : ℕ) (q : Fin 4 → ℝ) (i : Fin j) :
    alternatingMomentum (j + k) q (Fin.castAdd k (Fin.rev i)) =
      if j % 2 = 0 then -alternatingMomentum j q i else alternatingMomentum j q i := by
  have hi : i.val < j := i.isLt
  have hrev : (Fin.castAdd k (Fin.rev i)).val = j - 1 - i.val := by
    simp [Fin.val_rev]
    omega
  ext μ
  unfold alternatingMomentum
  simp only [hrev]
  rcases Nat.mod_two_eq_zero_or_one j with hj0 | hj1
  · rcases Nat.mod_two_eq_zero_or_one i.val with hi0 | hi1
    · have h1 : (j - 1 - i.val) % 2 ≠ 0 := by omega
      simp [hj0, hi0, h1]
    · have h1 : (j - 1 - i.val) % 2 = 0 := by omega
      have hi_ne : i.val % 2 ≠ 0 := by omega
      simp [hj0, hi_ne, h1]
  · have hj_ne : j % 2 ≠ 0 := by omega
    rcases Nat.mod_two_eq_zero_or_one i.val with hi0 | hi1
    · have h1 : (j - 1 - i.val) % 2 = 0 := by omega
      simp [hj_ne, hi0, h1]
    · have h1 : (j - 1 - i.val) % 2 ≠ 0 := by omega
      have hi_ne : i.val % 2 ≠ 0 := by omega
      simp [hj_ne, hi_ne, h1]

lemma alternatingMomentum_natAdd (j k : ℕ) (q : Fin 4 → ℝ) (i : Fin k) :
    alternatingMomentum (j + k) q (Fin.natAdd j i) =
      if j % 2 = 0 then alternatingMomentum k q i else -alternatingMomentum k q i := by
  ext μ
  dsimp [alternatingMomentum]
  rcases Nat.mod_two_eq_zero_or_one j with hj0 | hj1
  · rcases Nat.mod_two_eq_zero_or_one i.val with hi0 | hi1
    · have h1 : (j + i.val) % 2 = 0 := by omega
      simp [hj0, hi0, h1]
    · have h1 : (j + i.val) % 2 ≠ 0 := by omega
      have hi_ne : i.val % 2 ≠ 0 := by omega
      simp [hj0, hi_ne, h1]
  · have hj_ne : j % 2 ≠ 0 := by omega
    rcases Nat.mod_two_eq_zero_or_one i.val with hi0 | hi1
    · have h1 : (j + i.val) % 2 ≠ 0 := by omega
      simp [hj_ne, hi0, h1]
    · have h1 : (j + i.val) % 2 = 0 := by omega
      have hi_ne : i.val % 2 ≠ 0 := by omega
      simp [hj_ne, hi_ne, h1]

lemma sum_fin_split_rev (j k : ℕ) (f : Fin (j + k) → ℝ) :
    (∑ m : Fin (j + k), f m) =
      (∑ i : Fin j, f (Fin.castAdd k (Fin.rev i))) +
        (∑ i : Fin k, f (Fin.natAdd j i)) := by
  rw [Fin.sum_univ_add]
  congr 1
  exact (Equiv.sum_comp Fin.revPerm (fun i : Fin j => f (Fin.castAdd k i))).symm

lemma minkowskiInner_neg_left (u v : Fin 4 → ℝ) :
    minkowskiInner (-u) v = -minkowskiInner u v := by
  simp [minkowskiInner_explicit]
  ring

theorem minkowskiFourier_split_rev_mul (j k : ℕ)
    (fj : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (fk : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ)
    (g : SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ)
    (hg : ∀ x : Fin (j + k) → Fin 4 → ℝ,
      g x = (starRingEnd ℂ) (fj (fun i => x (Fin.castAdd k (Fin.rev i)))) *
        fk (fun i => x (Fin.natAdd j i)))
    (p : Fin (j + k) → Fin 4 → ℝ) :
    minkowskiFourier g p =
      (starRingEnd ℂ) (minkowskiFourier fj (fun i => -p (Fin.castAdd k (Fin.rev i)))) *
        minkowskiFourier fk (fun i => p (Fin.natAdd j i)) := by
  unfold minkowskiFourier
  have h_integrand :
      (fun x : Fin (j + k) → Fin 4 → ℝ =>
        g x * Complex.exp
          (-(Complex.I * ((∑ m : Fin (j + k), minkowskiInner (p m) (x m) : ℝ) : ℂ)))) =
      fun x : Fin (j + k) → Fin 4 → ℝ =>
        ((fun y : Fin j → Fin 4 → ℝ =>
          (starRingEnd ℂ) (fj y * Complex.exp (-(Complex.I *
            ((∑ i : Fin j, minkowskiInner (-p (Fin.castAdd k (Fin.rev i))) (y i) : ℝ) : ℂ)))))
          (fun i => x (Fin.castAdd k (Fin.rev i)))) *
        ((fun z : Fin k → Fin 4 → ℝ =>
          fk z * Complex.exp (-(Complex.I *
            ((∑ i : Fin k, minkowskiInner (p (Fin.natAdd j i)) (z i) : ℝ) : ℂ))))
          (fun i => x (Fin.natAdd j i))) := by
    ext x
    dsimp only
    rw [hg x, sum_fin_split_rev j k (fun m => minkowskiInner (p m) (x m)),
        Complex.ofReal_add, mul_add, neg_add, Complex.exp_add]
    have h_conj_exp :
        (starRingEnd ℂ) (fj (fun i => x (Fin.castAdd k (Fin.rev i))) *
          Complex.exp (-(Complex.I *
            ((∑ i : Fin j,
              minkowskiInner (-p (Fin.castAdd k (Fin.rev i)))
                (x (Fin.castAdd k (Fin.rev i))) : ℝ) : ℂ)))) =
        (starRingEnd ℂ) (fj (fun i => x (Fin.castAdd k (Fin.rev i)))) *
          Complex.exp (-(Complex.I *
            ((∑ i : Fin j,
              minkowskiInner (p (Fin.castAdd k (Fin.rev i)))
                (x (Fin.castAdd k (Fin.rev i))) : ℝ) : ℂ))) := by
      rw [map_mul, ← Complex.exp_conj]
      congr 2
      simp_rw [minkowskiInner_neg_left, Finset.sum_neg_distrib]
      rw [Complex.ofReal_neg, map_neg, map_mul, Complex.conj_I, map_neg, Complex.conj_ofReal]
      ring
    rw [h_conj_exp]
    ring
  rw [h_integrand, integral_split_rev_mul j k
    (fun y => (starRingEnd ℂ) (fj y * Complex.exp (-(Complex.I *
      ((∑ i : Fin j, minkowskiInner (-p (Fin.castAdd k (Fin.rev i))) (y i) : ℝ) : ℂ)))))
    (fun z => fk z * Complex.exp (-(Complex.I *
      ((∑ i : Fin k, minkowskiInner (p (Fin.natAdd j i)) (z i) : ℝ) : ℂ)))),
    integral_conj]

theorem fourMomentumW_apply_split_rev_mul (q : Fin 4 → ℝ) (j k : ℕ)
    (fj : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (fk : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ)
    (g : SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ)
    (hg : ∀ x : Fin (j + k) → Fin 4 → ℝ,
      g x = (starRingEnd ℂ) (fj (fun i => x (Fin.castAdd k (Fin.rev i)))) *
        fk (fun i => x (Fin.natAdd j i)))
    (α : Fin (j + k) → Unit) :
    fourMomentumW q (j + k) α g =
      (if j % 2 = 0 ∧ k % 2 = 0 then
        (starRingEnd ℂ) (minkowskiFourier fj (alternatingMomentum j q)) *
          minkowskiFourier fk (alternatingMomentum k q)
      else 0) +
      (if j % 2 = 1 ∧ k % 2 = 1 then
        (starRingEnd ℂ) (minkowskiFourier fj (-alternatingMomentum j q)) *
          minkowskiFourier fk (-alternatingMomentum k q)
      else 0) := by
  rw [fourMomentumW_apply]
  rcases Nat.mod_two_eq_zero_or_one j with hj0 | hj1 <;>
  rcases Nat.mod_two_eq_zero_or_one k with hk0 | hk1
  · have hjk : (j + k) % 2 = 0 := by omega
    have hj_not1 : ¬ (j % 2 = 1 ∧ k % 2 = 1) := by omega
    rw [if_pos hjk, if_pos ⟨hj0, hk0⟩, if_neg hj_not1, add_zero,
        minkowskiFourier_split_rev_mul j k fj fk g hg]
    have h_left :
        (fun i : Fin j => -alternatingMomentum (j + k) q (Fin.castAdd k (Fin.rev i))) =
          alternatingMomentum j q := by
      ext i μ
      rw [alternatingMomentum_castAdd_rev, if_pos hj0, Pi.neg_apply, Pi.neg_apply, neg_neg]
    have h_right :
        (fun i : Fin k => alternatingMomentum (j + k) q (Fin.natAdd j i)) =
          alternatingMomentum k q := by
      ext i μ
      rw [alternatingMomentum_natAdd, if_pos hj0]
    rw [h_left, h_right]
  · have hjk : (j + k) % 2 ≠ 0 := by omega
    have h1 : ¬ (j % 2 = 0 ∧ k % 2 = 0) := by omega
    have h2 : ¬ (j % 2 = 1 ∧ k % 2 = 1) := by omega
    rw [if_neg hjk, if_neg h1, if_neg h2, add_zero]
  · have hjk : (j + k) % 2 ≠ 0 := by omega
    have h1 : ¬ (j % 2 = 0 ∧ k % 2 = 0) := by omega
    have h2 : ¬ (j % 2 = 1 ∧ k % 2 = 1) := by omega
    rw [if_neg hjk, if_neg h1, if_neg h2, add_zero]
  · have hjk : (j + k) % 2 = 0 := by omega
    have hj_not0 : ¬ (j % 2 = 0 ∧ k % 2 = 0) := by omega
    have hj_ne0 : j % 2 ≠ 0 := by omega
    rw [if_pos hjk, if_neg hj_not0, if_pos ⟨hj1, hk1⟩, zero_add,
        minkowskiFourier_split_rev_mul j k fj fk g hg]
    have h_left :
        (fun i : Fin j => -alternatingMomentum (j + k) q (Fin.castAdd k (Fin.rev i))) =
          -alternatingMomentum j q := by
      ext i μ
      rw [alternatingMomentum_castAdd_rev, if_neg hj_ne0]
      rfl
    have h_right :
        (fun i : Fin k => alternatingMomentum (j + k) q (Fin.natAdd j i)) =
          -alternatingMomentum k q := by
      ext i μ
      rw [alternatingMomentum_natAdd, if_neg hj_ne0]
      rfl
    rw [h_left, h_right]

lemma sum_star_mul_eq_normSq {α : Type*} (s : Finset α) (f : α → ℂ) :
    (∑ a ∈ s, ∑ b ∈ s, (starRingEnd ℂ) (f a) * f b) =
      ((Complex.normSq (∑ a ∈ s, f a) : ℝ) : ℂ) := by
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul, ← map_sum]
  rw [mul_comm, Complex.mul_conj]

theorem fourMomentumW_positivity (q : Fin 4 → ℝ) :
    Positivity trivialStarStructure (fourMomentumW q) := by
  intro N F G hG
  let A_even : ℕ → ℂ := fun j =>
    if j % 2 = 0 then minkowskiFourier (F j default) (alternatingMomentum j q) else 0
  let A_odd : ℕ → ℂ := fun j =>
    if j % 2 = 1 then minkowskiFourier (F j default) (-alternatingMomentum j q) else 0
  have h_term : ∀ j k : ℕ,
      (∑ α : Fin j → Unit, ∑ α' : Fin k → Unit, ∑ β : Fin j → Unit,
        (∏ i, trivialStarStructure.C (α i) (β i)) *
          fourMomentumW q (j + k) (Fin.append (β ∘ Fin.rev) α') (G j k α α')) =
      (starRingEnd ℂ) (A_even j) * A_even k +
        (starRingEnd ℂ) (A_odd j) * A_odd k := by
    intro j k
    simp only [Fintype.sum_unique, trivialStarStructure, Matrix.one_apply_eq,
      Finset.prod_const_one, one_mul]
    rw [fourMomentumW_apply_split_rev_mul q j k (F j default) (F k default)
        (G j k default default) (hG j k default default)]
    dsimp [A_even, A_odd]
    by_cases hj0 : j % 2 = 0 <;> by_cases hk0 : k % 2 = 0
    · simp [hj0, hk0]
    · simp [hj0, hk0]
    · simp [hj0, hk0]
    · have hj1 : j % 2 = 1 := by omega
      have hk1 : k % 2 = 1 := by omega
      simp [hj1, hk1]
  simp_rw [h_term, Finset.sum_add_distrib,
      sum_star_mul_eq_normSq (Finset.range (N + 1)) A_even,
      sum_star_mul_eq_normSq (Finset.range (N + 1)) A_odd]
  have h_nonneg : 0 ≤
      Complex.normSq (∑ j ∈ Finset.range (N + 1), A_even j) +
        Complex.normSq (∑ j ∈ Finset.range (N + 1), A_odd j) :=
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  exact_mod_cast h_nonneg

lemma alternatingMomentum_rev_of_even (n : ℕ) (hn : n % 2 = 0) (q : Fin 4 → ℝ) (i : Fin n) :
    alternatingMomentum n q (Fin.rev i) = -alternatingMomentum n q i := by
  have hi : i.val < n := i.isLt
  have hrev : (Fin.rev i).val = n - 1 - i.val := by
    rw [Fin.val_rev]
    omega
  ext μ
  unfold alternatingMomentum
  simp only [hrev]
  rcases Nat.mod_two_eq_zero_or_one i.val with hi0 | hi1
  · have h1 : (n - 1 - i.val) % 2 ≠ 0 := by omega
    simp [hi0, h1]
  · have h1 : (n - 1 - i.val) % 2 = 0 := by omega
    have hi_ne : i.val % 2 ≠ 0 := by omega
    simp [hi_ne, h1]

lemma minkowskiInnerC_real_left_star_right (u : Fin 4 → ℝ) (w : Fin 4 → ℂ) :
    minkowskiInnerC (fun μ => (u μ : ℂ)) (fun μ => star (w μ)) =
      star (minkowskiInnerC (fun μ => (u μ : ℂ)) w) := by
  unfold minkowskiInnerC
  simp only [star_sub, star_mul', Complex.star_def, Complex.conj_ofReal]

lemma minkowskiInnerC_neg_real_left (u : Fin 4 → ℝ) (w : Fin 4 → ℂ) :
    minkowskiInnerC (fun μ => ((-u) μ : ℂ)) w =
      -minkowskiInnerC (fun μ => (u μ : ℂ)) w := by
  unfold minkowskiInnerC
  simp only [Pi.neg_apply, Complex.ofReal_neg]
  ring

theorem star_vladimirov_kernel_eq (n : ℕ) (z : Fin n → Fin 4 → ℂ) (p : Fin n → Fin 4 → ℝ) :
    star (vladimirov_kernel n z p) =
      vladimirov_kernel n (fun i μ => star (z (Fin.rev i) μ)) (fun i => -p (Fin.rev i)) := by
  unfold vladimirov_kernel
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  rw [map_mul, map_neg, Complex.conj_I, neg_neg, map_sum,
      ← Equiv.sum_comp Fin.revPerm, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h_rev : Fin.revPerm i = Fin.rev i := rfl
  have h_star : ((fun i μ => (starRingEnd ℂ) (z (Fin.rev i) μ)) i) =
      fun μ => star (z (Fin.rev i) μ) := rfl
  rw [h_rev, minkowskiInnerC_neg_real_left, h_star,
      minkowskiInnerC_real_left_star_right (p (Fin.rev i)) (z (Fin.rev i)),
      Complex.star_def]
  ring

theorem fourMomentumTubeWickHermiticity (q : Fin 4 → ℝ) :
    TubeWickHermiticity trivialStarStructure (fourMomentumTubeExtension q) := by
  intro n α z _hz _hstar
  simp only [Fintype.sum_unique, trivialStarStructure, Matrix.one_apply_eq,
    Finset.prod_const_one, one_mul, fourMomentumTubeExtension_H, fourMomentumH]
  by_cases hn : n % 2 = 0
  · rw [if_pos hn, if_pos hn, star_vladimirov_kernel_eq]
    congr 1
    ext i μ
    rw [alternatingMomentum_rev_of_even n hn q i, Pi.neg_apply, Pi.neg_apply, neg_neg]
  · simp [hn]

theorem fourMomentumOSHermiticity (q : Fin 4 → ℝ) :
    OSHermiticity trivialStarStructure (fourMomentumS q) :=
  schwingerFromTube_os_hermiticity trivialStarStructure (fourMomentumTubeExtension q)
    (fourMomentumTubeWickHermiticity q)

lemma sum_fin_split_rev_complex (j k : ℕ) (f : Fin (j + k) → ℂ) :
    (∑ m : Fin (j + k), f m) =
      (∑ i : Fin j, f (Fin.castAdd k (Fin.rev i))) +
        (∑ i : Fin k, f (Fin.natAdd j i)) := by
  rw [Fin.sum_univ_add]
  congr 1
  exact (Equiv.sum_comp Fin.revPerm (fun i : Fin j => f (Fin.castAdd k i))).symm

theorem vladimirov_kernel_wickEmbedN_osConcatPoint (j k : ℕ)
    (x : Fin j → Fin 4 → ℝ) (y : Fin k → Fin 4 → ℝ)
    (p : Fin (j + k) → Fin 4 → ℝ) :
    vladimirov_kernel (j + k) (wickEmbedN (j + k) (osConcatPoint j k x y)) p =
      star (vladimirov_kernel j (wickEmbedN j x)
        (fun i => -p (Fin.castAdd k (Fin.rev i)))) *
      vladimirov_kernel k (wickEmbedN k y)
        (fun i => p (Fin.natAdd j i)) := by
  unfold vladimirov_kernel
  rw [sum_fin_split_rev_complex j k
    (fun m => minkowskiInnerC (fun μ => (p m μ : ℂ))
      (wickEmbedN (j + k) (osConcatPoint j k x y) m)),
    mul_add, Complex.exp_add]
  congr 1
  · rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    rw [map_mul, map_neg, Complex.conj_I, neg_neg, map_sum,
        Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h_cast : wickEmbedN (j + k) (osConcatPoint j k x y) (Fin.castAdd k (Fin.rev i)) =
        fun μ => star (wickEmbedN j x i μ) := by
      ext μ
      change wickEmbed (osConcatPoint j k x y (Fin.castAdd k (Fin.rev i))) μ =
        star (wickEmbed (x i) μ)
      rw [osConcatPoint_castAdd, Fin.rev_rev, ← star_wickEmbed]
    rw [h_cast, minkowskiInnerC_real_left_star_right, minkowskiInnerC_neg_real_left,
        Complex.star_def, map_neg]
    ring
  · congr 1
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h_nat : wickEmbedN (j + k) (osConcatPoint j k x y) (Fin.natAdd j i) =
        wickEmbedN k y i := by
      ext μ
      dsimp [wickEmbedN]
      rw [osConcatPoint_natAdd]
    rw [h_nat]

theorem fourMomentumS_osConcatPoint (q : Fin 4 → ℝ) (j k : ℕ)
    (x : Fin j → Fin 4 → ℝ) (y : Fin k → Fin 4 → ℝ)
    (α : Fin (j + k) → Unit) :
    fourMomentumS q (j + k) α (osConcatPoint j k x y) =
      (if j % 2 = 0 ∧ k % 2 = 0 then
        star (vladimirov_kernel j (wickEmbedN j x) (alternatingMomentum j q)) *
          vladimirov_kernel k (wickEmbedN k y) (alternatingMomentum k q)
      else 0) +
      (if j % 2 = 1 ∧ k % 2 = 1 then
        star (vladimirov_kernel j (wickEmbedN j x) (-alternatingMomentum j q)) *
          vladimirov_kernel k (wickEmbedN k y) (-alternatingMomentum k q)
      else 0) := by
  rw [fourMomentumS_apply, fourMomentumH]
  rcases Nat.mod_two_eq_zero_or_one j with hj0 | hj1 <;>
  rcases Nat.mod_two_eq_zero_or_one k with hk0 | hk1
  · have hjk : (j + k) % 2 = 0 := by omega
    have hj_not1 : ¬ (j % 2 = 1 ∧ k % 2 = 1) := by omega
    rw [if_pos hjk, if_pos ⟨hj0, hk0⟩, if_neg hj_not1, add_zero,
        vladimirov_kernel_wickEmbedN_osConcatPoint]
    have h_left :
        (fun i : Fin j => -alternatingMomentum (j + k) q (Fin.castAdd k (Fin.rev i))) =
          alternatingMomentum j q := by
      ext i μ
      rw [alternatingMomentum_castAdd_rev, if_pos hj0, Pi.neg_apply, Pi.neg_apply, neg_neg]
    have h_right :
        (fun i : Fin k => alternatingMomentum (j + k) q (Fin.natAdd j i)) =
          alternatingMomentum k q := by
      ext i μ
      rw [alternatingMomentum_natAdd, if_pos hj0]
    rw [h_left, h_right]
  · have hjk : (j + k) % 2 ≠ 0 := by omega
    have h1 : ¬ (j % 2 = 0 ∧ k % 2 = 0) := by omega
    have h2 : ¬ (j % 2 = 1 ∧ k % 2 = 1) := by omega
    rw [if_neg hjk, if_neg h1, if_neg h2, add_zero]
  · have hjk : (j + k) % 2 ≠ 0 := by omega
    have h1 : ¬ (j % 2 = 0 ∧ k % 2 = 0) := by omega
    have h2 : ¬ (j % 2 = 1 ∧ k % 2 = 1) := by omega
    rw [if_neg hjk, if_neg h1, if_neg h2, add_zero]
  · have hjk : (j + k) % 2 = 0 := by omega
    have hj_not0 : ¬ (j % 2 = 0 ∧ k % 2 = 0) := by omega
    have hj_ne0 : j % 2 ≠ 0 := by omega
    rw [if_pos hjk, if_neg hj_not0, if_pos ⟨hj1, hk1⟩, zero_add,
        vladimirov_kernel_wickEmbedN_osConcatPoint]
    have h_left :
        (fun i : Fin j => -alternatingMomentum (j + k) q (Fin.castAdd k (Fin.rev i))) =
          -alternatingMomentum j q := by
      ext i μ
      rw [alternatingMomentum_castAdd_rev, if_neg hj_ne0]
      rfl
    have h_right :
        (fun i : Fin k => alternatingMomentum (j + k) q (Fin.natAdd j i)) =
          -alternatingMomentum k q := by
      ext i μ
      rw [alternatingMomentum_natAdd, if_neg hj_ne0]
      rfl
    rw [h_left, h_right]

noncomputable def fourMomentumEvenConfigTerm (q : Fin 4 → ℝ) (A : OSConfig Unit) : ℂ :=
  if A.1 % 2 = 0 then
    vladimirov_kernel A.1 (wickEmbedN A.1 A.2.2.val) (alternatingMomentum A.1 q)
  else 0

noncomputable def fourMomentumOddConfigTerm (q : Fin 4 → ℝ) (A : OSConfig Unit) : ℂ :=
  if A.1 % 2 = 1 then
    vladimirov_kernel A.1 (wickEmbedN A.1 A.2.2.val) (-alternatingMomentum A.1 q)
  else 0

theorem osKernel_fourMomentumS_eq (q : Fin 4 → ℝ) (A B : OSConfig Unit) :
    osKernel trivialStarStructure (fourMomentumS q) A B =
      star (fourMomentumEvenConfigTerm q A) * fourMomentumEvenConfigTerm q B +
        star (fourMomentumOddConfigTerm q A) * fourMomentumOddConfigTerm q B := by
  rcases A with ⟨j, α, x, hx⟩
  rcases B with ⟨k, α', y, hy⟩
  unfold osKernel fourMomentumEvenConfigTerm fourMomentumOddConfigTerm
  simp only [Fintype.sum_unique, trivialStarStructure, Matrix.one_apply_eq,
    Finset.prod_const_one, one_mul]
  rw [fourMomentumS_osConcatPoint]
  by_cases hj0 : j % 2 = 0 <;> by_cases hk0 : k % 2 = 0
  · simp [hj0, hk0]
  · simp [hj0, hk0]
  · simp [hj0, hk0]
  · have hj1 : j % 2 = 1 := by omega
    have hk1 : k % 2 = 1 := by omega
    simp [hj1, hk1]

theorem fourMomentumOSReflectionPositive (q : Fin 4 → ℝ) :
    OSReflectionPositive trivialStarStructure (fourMomentumS q) := by
  intro Ψ
  unfold osPreInner Finsupp.sum
  simp_rw [osKernel_fourMomentumS_eq]
  let f_even : OSConfig Unit → ℂ := fun A => Ψ A * fourMomentumEvenConfigTerm q A
  let f_odd : OSConfig Unit → ℂ := fun A => Ψ A * fourMomentumOddConfigTerm q A
  have h_split : ∀ A B : OSConfig Unit,
      star (Ψ A) * Ψ B *
        (star (fourMomentumEvenConfigTerm q A) * fourMomentumEvenConfigTerm q B +
          star (fourMomentumOddConfigTerm q A) * fourMomentumOddConfigTerm q B) =
      (starRingEnd ℂ) (f_even A) * f_even B +
        (starRingEnd ℂ) (f_odd A) * f_odd B := by
    intro A B
    dsimp [f_even, f_odd]
    simp only [map_mul]
    ring
  simp_rw [h_split, Finset.sum_add_distrib,
      sum_star_mul_eq_normSq Ψ.support f_even,
      sum_star_mul_eq_normSq Ψ.support f_odd]
  have h_nonneg : 0 ≤
      Complex.normSq (∑ A ∈ Ψ.support, f_even A) +
        Complex.normSq (∑ A ∈ Ψ.support, f_odd A) :=
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  exact_mod_cast h_nonneg

noncomputable def fourMomentumOSData (q : Fin 4 → ℝ) :
    OSReflectionPositiveData trivialRep trivialStarStructure where
  𝒮 := fourMomentumS q
  hermiticity := fourMomentumOSHermiticity q
  positivity := fourMomentumOSReflectionPositive q

@[simp]
lemma fourMomentumOSData_S (q : Fin 4 → ℝ) :
    (fourMomentumOSData q).𝒮 = fourMomentumS q := rfl

lemma norm_fourMomentumEvenConfigTerm_le_one {q : Fin 4 → ℝ}
    (hq : q ∈ closure forward_light_cone) (A : OSConfig Unit) :
    ‖fourMomentumEvenConfigTerm q A‖ ≤ 1 := by
  unfold fourMomentumEvenConfigTerm
  by_cases h : A.1 % 2 = 0
  · rw [if_pos h]
    exact vladimirov_kernel_norm_le_one_of_forwardConeSpectralRegion A.1
      (alternatingMomentum A.1 q)
      (alternatingMomentum_mem_forwardConeSpectralRegion A.1 h hq)
      (wickEmbedN A.1 A.2.2.val)
      (wickEmbedN_mem_forward_tube_n A.1 A.2.2.property.2)
  · rw [if_neg h, norm_zero]
    exact zero_le_one

lemma sum_neg_alternatingMomentum_of_odd (n : ℕ) (hn : n % 2 = 1) (q : Fin 4 → ℝ) :
    ∑ i : Fin n, (-alternatingMomentum n q) i = -q := by
  change (∑ i : Fin n, -(if i.val % 2 = 0 then q else -q)) = -q
  rw [Finset.sum_neg_distrib,
      Fin.sum_univ_eq_sum_range (fun j => if j % 2 = 0 then q else -q) n,
      sum_range_alternating n q]
  have hn_ne : n % 2 ≠ 0 := by omega
  rw [if_neg hn_ne]

lemma vladimirov_kernel_shift_of_sum (n : ℕ) (p : Fin n → Fin 4 → ℝ)
    (z : Fin n → Fin 4 → ℂ) (a : Fin 4 → ℂ) :
    vladimirov_kernel n (fun i => z i + a) p =
      vladimirov_kernel n z p *
        Complex.exp (-Complex.I * minkowskiInnerC (fun μ => ((∑ i : Fin n, p i) μ : ℂ)) a) := by
  unfold vladimirov_kernel
  rw [← Complex.exp_add]
  congr 1
  have h_add : ∀ k : Fin n,
      minkowskiInnerC (fun μ => (p k μ : ℂ)) (z k + a) =
        minkowskiInnerC (fun μ => (p k μ : ℂ)) (z k) +
          minkowskiInnerC (fun μ => (p k μ : ℂ)) a := by
    intro k
    dsimp [minkowskiInnerC]
    ring
  simp_rw [h_add, Finset.sum_add_distrib, mul_add]
  congr 1
  congr 1
  dsimp [minkowskiInnerC]
  simp only [Finset.sum_apply, Complex.ofReal_sum, Finset.sum_mul, Finset.sum_sub_distrib]

lemma minkowskiInnerC_neg_real_wickEmbed_euclidTimeVec (q : Fin 4 → ℝ) (τ : ℝ) :
    -Complex.I * minkowskiInnerC (fun μ => ((-q) μ : ℂ)) (wickEmbed (euclidTimeVec τ)) =
      ((-(τ * q 0) : ℝ) : ℂ) := by
  dsimp [minkowskiInnerC, wickEmbed, euclidTimeVec]
  simp only [Fin.isValue, Complex.ofReal_neg, Complex.ofReal_mul]
  linear_combination (q 0 : ℂ) * (τ : ℂ) * Complex.I_sq

theorem fourMomentumEvenConfigTerm_timeShift (q : Fin 4 → ℝ)
    (τ : ℝ) (hτ : 0 ≤ τ) (A : OSConfig Unit) :
    fourMomentumEvenConfigTerm q (osConfigTimeShift τ hτ A) =
      fourMomentumEvenConfigTerm q A := by
  rcases A with ⟨n, α, x, hx⟩
  unfold fourMomentumEvenConfigTerm osConfigTimeShift
  dsimp only
  by_cases hn : n % 2 = 0
  · rw [if_pos hn, if_pos hn]
    have h_wick : wickEmbedN n (fun i => x i + euclidTimeVec τ) =
        fun i => wickEmbedN n x i + wickEmbed (euclidTimeVec τ) := by
      ext i μ
      exact congrFun (wickEmbed_add (x i) (euclidTimeVec τ)) μ
    rw [h_wick]
    exact vladimirov_kernel_add_const_of_sum_eq_zero n
      (sum_alternatingMomentum_of_even n hn q) (wickEmbedN n x) (wickEmbed (euclidTimeVec τ))
  · simp [hn]

theorem fourMomentumOddConfigTerm_timeShift (q : Fin 4 → ℝ)
    (τ : ℝ) (hτ : 0 ≤ τ) (A : OSConfig Unit) :
    fourMomentumOddConfigTerm q (osConfigTimeShift τ hτ A) =
      fourMomentumOddConfigTerm q A * ((Real.exp (-(τ * q 0)) : ℝ) : ℂ) := by
  rcases A with ⟨n, α, x, hx⟩
  unfold fourMomentumOddConfigTerm osConfigTimeShift
  dsimp only
  by_cases hn : n % 2 = 1
  · rw [if_pos hn, if_pos hn]
    have h_wick : wickEmbedN n (fun i => x i + euclidTimeVec τ) =
        fun i => wickEmbedN n x i + wickEmbed (euclidTimeVec τ) := by
      ext i μ
      exact congrFun (wickEmbed_add (x i) (euclidTimeVec τ)) μ
    rw [h_wick, vladimirov_kernel_shift_of_sum,
        sum_neg_alternatingMomentum_of_odd n hn q,
        minkowskiInnerC_neg_real_wickEmbed_euclidTimeVec,
        Complex.ofReal_exp]
  · rw [if_neg hn, if_neg hn, zero_mul]

@[simp]
lemma fourMomentumEvenConfigTerm_vacuum (q : Fin 4 → ℝ) :
    fourMomentumEvenConfigTerm q (osVacuumConfig Unit) = 1 := by
  unfold fourMomentumEvenConfigTerm osVacuumConfig vladimirov_kernel
  simp

@[simp]
lemma fourMomentumOddConfigTerm_vacuum (q : Fin 4 → ℝ) :
    fourMomentumOddConfigTerm q (osVacuumConfig Unit) = 0 := by
  unfold fourMomentumOddConfigTerm osVacuumConfig
  simp

theorem osKernel_fourMomentumS_timeShift (q : Fin 4 → ℝ)
    (τ : ℝ) (hτ : 0 ≤ τ) (A B : OSConfig Unit) :
    osKernel trivialStarStructure (fourMomentumS q) A (osConfigTimeShift τ hτ B) =
      osKernel trivialStarStructure (fourMomentumS q) A (osVacuumConfig Unit) *
        osKernel trivialStarStructure (fourMomentumS q) (osVacuumConfig Unit) B +
      star (fourMomentumOddConfigTerm q A) * fourMomentumOddConfigTerm q B *
        ((Real.exp (-(τ * q 0)) : ℝ) : ℂ) := by
  rw [osKernel_fourMomentumS_eq q A (osConfigTimeShift τ hτ B),
      osKernel_fourMomentumS_eq q A (osVacuumConfig Unit),
      osKernel_fourMomentumS_eq q (osVacuumConfig Unit) B,
      fourMomentumEvenConfigTerm_timeShift,
      fourMomentumOddConfigTerm_timeShift,
      fourMomentumEvenConfigTerm_vacuum,
      fourMomentumOddConfigTerm_vacuum]
  simp only [mul_one, mul_zero, add_zero, star_one, star_zero, one_mul, zero_mul,
    mul_assoc]

theorem fourMomentumOSTimeCluster {q : Fin 4 → ℝ} (hq0 : 0 < q 0) :
    OSTimeClusterDecomposition (fourMomentumOSData q) := by
  intro A B
  let L : ℂ := osKernel trivialStarStructure (fourMomentumS q) A (osVacuumConfig Unit) *
    osKernel trivialStarStructure (fourMomentumS q) (osVacuumConfig Unit) B
  let C : ℂ := star (fourMomentumOddConfigTerm q A) * fourMomentumOddConfigTerm q B
  change Tendsto
    (fun τ : ℝ =>
      osKernel trivialStarStructure (fourMomentumS q) A
        (osConfigTimeShift (max τ 0) (le_max_right τ 0) B))
    atTop (𝓝 L)
  simp_rw [osKernel_fourMomentumS_timeShift]
  change Tendsto
    (fun τ : ℝ => L + C * ((Real.exp (-(max τ 0 * q 0)) : ℝ) : ℂ))
    atTop (𝓝 L)
  have h_ev : (fun τ : ℝ => ((Real.exp (-(max τ 0 * q 0)) : ℝ) : ℂ)) =ᶠ[atTop]
      (fun τ : ℝ => ((Real.exp (τ * (-q 0)) : ℝ) : ℂ)) := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with τ hτ
    rw [max_eq_left hτ]
    congr 2
    ring
  have h_atBot : Tendsto (fun τ : ℝ => τ * (-q 0)) atTop atBot :=
    Filter.Tendsto.atTop_mul_const_of_neg (neg_lt_zero.mpr hq0) tendsto_id
  have h_exp : Tendsto (fun τ : ℝ => Real.exp (τ * (-q 0))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp h_atBot
  have h_expC0 : Tendsto (fun τ : ℝ => ((Real.exp (τ * (-q 0)) : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp h_exp
  have h_expC : Tendsto (fun τ : ℝ => ((Real.exp (-(max τ 0 * q 0)) : ℝ) : ℂ)) atTop (𝓝 0) :=
    Tendsto.congr' h_ev.symm h_expC0
  simpa using tendsto_const_nhds.add (Tendsto.const_mul C h_expC)

theorem fourMomentumOSDiagonalKernelBounded {q : Fin 4 → ℝ} (hq0 : 0 ≤ q 0) :
    OSDiagonalKernelBounded trivialStarStructure (fourMomentumS q) := by
  intro A
  let cA : ℝ := ‖star (fourMomentumEvenConfigTerm q A) * fourMomentumEvenConfigTerm q A‖ +
    ‖star (fourMomentumOddConfigTerm q A) * fourMomentumOddConfigTerm q A‖
  refine ⟨cA, fun τ hτ => ?_⟩
  rw [osKernel_fourMomentumS_eq,
      fourMomentumEvenConfigTerm_timeShift,
      fourMomentumOddConfigTerm_timeShift]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  have h_assoc :
      star (fourMomentumOddConfigTerm q A * ((Real.exp (-(τ * q 0)) : ℝ) : ℂ)) *
        (fourMomentumOddConfigTerm q A * ((Real.exp (-(τ * q 0)) : ℝ) : ℂ)) =
      (star (fourMomentumOddConfigTerm q A) * fourMomentumOddConfigTerm q A) *
        (((Real.exp (-(τ * q 0)) : ℝ) : ℂ) * ((Real.exp (-(τ * q 0)) : ℝ) : ℂ)) := by
    rw [star_mul', Complex.star_def, Complex.conj_ofReal]
    ring
  rw [h_assoc, norm_mul, norm_mul (a := ((Real.exp (-(τ * q 0)) : ℝ) : ℂ))]
  have h_norm_exp : ‖((Real.exp (-(τ * q 0)) : ℝ) : ℂ)‖ = Real.exp (-(τ * q 0)) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [h_norm_exp]
  have h_exp_le : Real.exp (-(τ * q 0)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have h_prod_le : Real.exp (-(τ * q 0)) * Real.exp (-(τ * q 0)) ≤ 1 :=
    mul_le_one₀ h_exp_le (Real.exp_pos _).le h_exp_le
  exact mul_le_of_le_one_right (norm_nonneg _) h_prod_le

theorem fourMomentumOSContraction {q : Fin 4 → ℝ} (hq0 : 0 ≤ q 0) :
    OSContractionCondition (fourMomentumOSData q) :=
  osContractionCondition_of_diagonalKernelBounded (fourMomentumOSData q)
    (fourMomentumOSTranslationInvariant q) (fourMomentumOSDiagonalKernelBounded hq0)

theorem fourMomentumS_contDiffOn (q : Fin 4 → ℝ) (n : ℕ) (α : Fin n → Unit) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fourMomentumS q n α) (orderedEuclidN n) :=
  schwingerFromTube_contDiffOn (fourMomentumTubeExtension q) n α

lemma minkowskiInnerC_neg_right (u : Fin 4 → ℝ) (w : Fin 4 → ℂ) :
    minkowskiInnerC (fun μ => (u μ : ℂ)) (fun μ => -w μ) =
      -minkowskiInnerC (fun μ => (u μ : ℂ)) w := by
  unfold minkowskiInnerC
  ring

theorem fourMomentumTubeWeakLocality_one (q : Fin 4 → ℝ) :
    TubeWeakLocality 1 (fourMomentumTubeExtension q) := by
  intro n α z _hz
  rw [one_pow, one_mul]
  change fourMomentumH q n α (-(z ∘ Fin.rev)) = fourMomentumH q n (α ∘ Fin.rev) z
  unfold fourMomentumH
  by_cases hn : n % 2 = 0
  · rw [if_pos hn, if_pos hn]
    unfold vladimirov_kernel
    congr 1
    rw [← Equiv.sum_comp Fin.revPerm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h_rev : Fin.revPerm i = Fin.rev i := rfl
    rw [h_rev, alternatingMomentum_rev_of_even n hn q i]
    have h_z : (-(z ∘ Fin.rev)) (Fin.rev i) = fun μ => -z i μ := by
      ext μ
      change -(z (Fin.rev (Fin.rev i)) μ) = -z i μ
      rw [Fin.rev_rev]
    rw [h_z, minkowskiInnerC_neg_real_left, minkowskiInnerC_neg_right, neg_neg]
  · simp [hn]

theorem fourMomentumOSSymmetric (q : Fin 4 → ℝ)
    (n : ℕ) (α : Fin n → Unit) (x : Fin n → Fin 4 → ℝ) (hx : x ∈ orderedEuclidN n) :
    fourMomentumS q n α (-(x ∘ Fin.rev)) =
      (1 : ℂ) ^ (n * (n - 1) / 2) * fourMomentumS q n (α ∘ Fin.rev) x :=
  schwingerFromTube_weakLocality (fourMomentumTubeExtension q)
    (fourMomentumTubeWeakLocality_one q) n α x hx

theorem fourMomentumW_pct (q : Fin 4 → ℝ) :
    WightmanPCT 1 trivialRep (fourMomentumW q) :=
  wightman_pct_trivialRep_of_tube (fourMomentumTubeExtension q)
    (fourMomentumTubeTranslationInvariant q) (fourMomentumTubeWeakLocality_one q)

lemma norm_fourMomentumS_two_eq (q : Fin 4 → ℝ) (α : Fin 2 → Unit) (x : Fin 2 → Fin 4 → ℝ) :
    ‖fourMomentumS q 2 α x‖ = Real.exp (-(x 1 0 - x 0 0) * q 0) := by
  rw [fourMomentumS_two_eq, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le, Complex.norm_exp]
  have h_re : (-Complex.I *
      (((x 1 1 - x 0 1) * q 1 +
        (x 1 2 - x 0 2) * q 2 +
        (x 1 3 - x 0 3) * q 3 : ℝ) : ℂ)).re = 0 := by
    simp
  rw [h_re, Real.exp_zero, mul_one]

lemma zero_apply_ne_zero_of_mem_closed_forward_light_cone
    {q : Fin 4 → ℝ} (hq : q ∈ closed_forward_light_cone) (hne : q ≠ 0) :
    q 0 ≠ 0 := by
  intro hq0
  have hqq : 0 ≤ minkowskiInner q q := hq.2
  rw [minkowskiInner_explicit, hq0] at hqq
  have h1 : q 1 = 0 := by nlinarith [sq_nonneg (q 1), sq_nonneg (q 2), sq_nonneg (q 3)]
  have h2 : q 2 = 0 := by nlinarith [sq_nonneg (q 1), sq_nonneg (q 2), sq_nonneg (q 3)]
  have h3 : q 3 = 0 := by nlinarith [sq_nonneg (q 1), sq_nonneg (q 2), sq_nonneg (q 3)]
  apply hne
  ext μ
  fin_cases μ
  · exact hq0
  · exact h1
  · exact h2
  · exact h3

lemma zero_apply_ne_zero_of_mem_closure_forward_light_cone
    {q : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone) (hne : q ≠ 0) :
    q 0 ≠ 0 :=
  zero_apply_ne_zero_of_mem_closed_forward_light_cone
    (closure_forward_light_cone_subset hq) hne

theorem not_euclidRotCovariant_fourMomentumS_of_zero_apply_ne_zero
    {q : Fin 4 → ℝ} (hq0 : q 0 ≠ 0) :
    ¬ EuclidRotCovariant trivialRep (fourMomentumS q) := by
  intro h_euclid_rot
  let θ : ℝ := Real.pi / 3
  let x : Fin 2 → Fin 4 → ℝ := euclidOrderedBasePoint 2
  have hx : x ∈ orderedEuclidN 2 := euclidOrderedBasePoint_mem_orderedEuclidN 2
  have h_cos : Real.cos θ = 1 / 2 := Real.cos_pi_div_three
  have h_sin : Real.sin θ = Real.sqrt 3 / 2 := Real.sin_pi_div_three
  have h_rot_apply : ∀ i : Fin 2,
      euclidRotN 2 (boostHalfSU2 θ) (boostHalfSU2 θ) x i =
        ![1 / 2 * ((i.val : ℝ) + 1), 0, 0, Real.sqrt 3 / 2 * ((i.val : ℝ) + 1)] := by
    intro i
    change (euclidRotOfSU2 (boostHalfSU2 θ) (boostHalfSU2 θ)).mulVec (x i) = _
    rw [euclidRotOfSU2_mulVec, euclidRotApply_boostHalfSU2]
    dsimp [x, euclidOrderedBasePoint]
    rw [h_cos, h_sin]
    ext μ
    fin_cases μ <;> simp
  have hRx : euclidRotN 2 (boostHalfSU2 θ) (boostHalfSU2 θ) x ∈ orderedEuclidN 2 := by
    intro i hi
    rw [h_rot_apply ⟨i.val, i.isLt⟩, h_rot_apply ⟨i.val + 1, hi⟩]
    simp only [Matrix.cons_val_zero]
    have hlt : (i.val : ℝ) < ((i.val + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_succ_self i.val
    linarith
  let α₀ : Fin 2 → Unit := default
  have h_eq := h_euclid_rot 2 (boostHalfSU2 θ) (boostHalfSU2 θ) x hx hRx α₀
  have h_prod :
      (∏ i : Fin 2,
        trivialRep.σ (su2ToSL2C (boostHalfSU2 θ), su2ToSL2C (boostHalfSU2 θ))
          (α₀ i) (α₀ i)) = 1 :=
    Finset.prod_eq_one (fun i _ => rfl)
  rw [Fintype.sum_unique, h_prod, one_mul] at h_eq
  change fourMomentumS q 2 α₀ (euclidRotN 2 (boostHalfSU2 θ) (boostHalfSU2 θ) x) =
    fourMomentumS q 2 α₀ x at h_eq
  have h_norm := congrArg norm h_eq
  rw [norm_fourMomentumS_two_eq, norm_fourMomentumS_two_eq] at h_norm
  have h_time_x : x 1 0 - x 0 0 = 1 := euclidOrderedBasePoint_two_time_diff
  have h_time_rot :
      euclidRotN 2 (boostHalfSU2 θ) (boostHalfSU2 θ) x 1 0 -
        euclidRotN 2 (boostHalfSU2 θ) (boostHalfSU2 θ) x 0 0 = 1 / 2 := by
    rw [h_rot_apply 1, h_rot_apply 0]
    norm_num
  rw [h_time_x, h_time_rot] at h_norm
  have h_arg := Real.exp_injective h_norm
  apply hq0
  linarith

noncomputable def fourMomentumSpatialPhase (q : Fin 4 → ℝ) (a : Fin 3 → ℝ) : ℂ :=
  Complex.exp (-Complex.I *
    minkowskiInnerC (fun μ => ((-q) μ : ℂ)) (wickEmbed (euclidSpatialVec a)))

@[simp]
lemma fourMomentumSpatialPhase_zero (q : Fin 4 → ℝ) :
    fourMomentumSpatialPhase q 0 = 1 := by
  simp [fourMomentumSpatialPhase, euclidSpatialVec_zero, minkowskiInnerC]

@[simp]
lemma star_mul_fourMomentumSpatialPhase (q : Fin 4 → ℝ) (a : Fin 3 → ℝ) :
    star (fourMomentumSpatialPhase q a) * fourMomentumSpatialPhase q a = 1 := by
  unfold fourMomentumSpatialPhase
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  have h_arg :
      (starRingEnd ℂ)
          (-Complex.I * minkowskiInnerC (fun μ => ((-q) μ : ℂ))
            (wickEmbed (euclidSpatialVec a))) +
        (-Complex.I * minkowskiInnerC (fun μ => ((-q) μ : ℂ))
          (wickEmbed (euclidSpatialVec a))) = 0 := by
    dsimp [minkowskiInnerC, wickEmbed]
    simp only [Fin.isValue, Complex.ofReal_neg, zero_mul, mul_zero,
      map_mul, map_neg, map_zero, Complex.conj_I, map_sub, Complex.conj_ofReal]
    ring
  rw [h_arg, Complex.exp_zero]

@[simp]
lemma fourMomentumEvenConfigTerm_osBaseConfig_one (q : Fin 4 → ℝ) :
    fourMomentumEvenConfigTerm q (osBaseConfig 1) = 0 := by
  unfold fourMomentumEvenConfigTerm osBaseConfig
  simp

@[simp]
lemma fourMomentumOddConfigTerm_osBaseConfig_one (q : Fin 4 → ℝ) :
    fourMomentumOddConfigTerm q (osBaseConfig 1) = ((Real.exp (-q 0) : ℝ) : ℂ) := by
  unfold fourMomentumOddConfigTerm osBaseConfig vladimirov_kernel
  dsimp only
  rw [if_pos rfl, Fin.sum_univ_one, Complex.ofReal_exp]
  congr 1
  dsimp [alternatingMomentum, wickEmbedN, wickEmbed, euclidOrderedBasePoint, minkowskiInnerC]
  simp only [Fin.isValue, Nat.cast_zero, zero_add,
    Complex.ofReal_neg, Complex.ofReal_one, mul_zero, sub_zero]
  linear_combination (q 0 : ℂ) * Complex.I_sq

theorem fourMomentumEvenConfigTerm_spatialShift (q : Fin 4 → ℝ)
    (a : Fin 3 → ℝ) (A : OSConfig Unit) :
    fourMomentumEvenConfigTerm q (osConfigSpatialShift a A) =
      fourMomentumEvenConfigTerm q A := by
  rcases A with ⟨n, α, x, hx⟩
  unfold fourMomentumEvenConfigTerm osConfigSpatialShift
  dsimp only
  by_cases hn : n % 2 = 0
  · rw [if_pos hn, if_pos hn]
    have h_wick : wickEmbedN n (fun i => x i + euclidSpatialVec a) =
        fun i => wickEmbedN n x i + wickEmbed (euclidSpatialVec a) := by
      ext i μ
      exact congrFun (wickEmbed_add (x i) (euclidSpatialVec a)) μ
    rw [h_wick]
    exact vladimirov_kernel_add_const_of_sum_eq_zero n
      (sum_alternatingMomentum_of_even n hn q) (wickEmbedN n x) (wickEmbed (euclidSpatialVec a))
  · simp [hn]

theorem fourMomentumOddConfigTerm_spatialShift (q : Fin 4 → ℝ)
    (a : Fin 3 → ℝ) (A : OSConfig Unit) :
    fourMomentumOddConfigTerm q (osConfigSpatialShift a A) =
      fourMomentumOddConfigTerm q A * fourMomentumSpatialPhase q a := by
  rcases A with ⟨n, α, x, hx⟩
  unfold fourMomentumOddConfigTerm osConfigSpatialShift fourMomentumSpatialPhase
  dsimp only
  by_cases hn : n % 2 = 1
  · rw [if_pos hn, if_pos hn]
    have h_wick : wickEmbedN n (fun i => x i + euclidSpatialVec a) =
        fun i => wickEmbedN n x i + wickEmbed (euclidSpatialVec a) := by
      ext i μ
      exact congrFun (wickEmbed_add (x i) (euclidSpatialVec a)) μ
    rw [h_wick, vladimirov_kernel_shift_of_sum,
        sum_neg_alternatingMomentum_of_odd n hn q]
  · rw [if_neg hn, if_neg hn, zero_mul]

noncomputable def fourMomentumOneParticlePre (q : Fin 4 → ℝ) :
    OSPreHilbertSpace (fourMomentumOSData q) :=
  ((Real.exp (q 0) : ℝ) : ℂ) • osBasisPre (fourMomentumOSData q) (osBaseConfig 1)

noncomputable def fourMomentumOneParticle (q : Fin 4 → ℝ) :
    OSHilbert (fourMomentumOSData q) :=
  toOSHilbert (fourMomentumOSData q) (fourMomentumOneParticlePre q)

lemma fourMomentumOneParticle_eq_smul_osBasis (q : Fin 4 → ℝ) :
    fourMomentumOneParticle q =
      ((Real.exp (q 0) : ℝ) : ℂ) • osBasis (fourMomentumOSData q) (osBaseConfig 1) :=
  (toOSHilbert (fourMomentumOSData q)).map_smul _ _

@[simp]
lemma inner_osBasisPre_fourMomentumOSData (q : Fin 4 → ℝ) (A B : OSConfig Unit) :
    ⟪osBasisPre (fourMomentumOSData q) A, osBasisPre (fourMomentumOSData q) B⟫_ℂ =
      star (fourMomentumEvenConfigTerm q A) * fourMomentumEvenConfigTerm q B +
        star (fourMomentumOddConfigTerm q A) * fourMomentumOddConfigTerm q B := by
  rw [inner_osBasisPre, fourMomentumOSData_S, osKernel_fourMomentumS_eq]

@[simp]
lemma inner_osVacuumPre_fourMomentumOSData_osBasisPre (q : Fin 4 → ℝ) (A : OSConfig Unit) :
    ⟪osVacuumPre (fourMomentumOSData q), osBasisPre (fourMomentumOSData q) A⟫_ℂ =
      fourMomentumEvenConfigTerm q A := by
  unfold osVacuumPre
  rw [inner_osBasisPre_fourMomentumOSData]
  simp

@[simp]
lemma inner_osBasisPre_osVacuumPre_fourMomentumOSData (q : Fin 4 → ℝ) (A : OSConfig Unit) :
    ⟪osBasisPre (fourMomentumOSData q) A, osVacuumPre (fourMomentumOSData q)⟫_ℂ =
      star (fourMomentumEvenConfigTerm q A) := by
  unfold osVacuumPre
  rw [inner_osBasisPre_fourMomentumOSData]
  simp

@[simp]
lemma inner_osVacuumPre_fourMomentumOSData_self (q : Fin 4 → ℝ) :
    ⟪osVacuumPre (fourMomentumOSData q), osVacuumPre (fourMomentumOSData q)⟫_ℂ = 1 := by
  change ⟪osVacuumPre (fourMomentumOSData q),
    osBasisPre (fourMomentumOSData q) (osVacuumConfig Unit)⟫_ℂ = 1
  rw [inner_osVacuumPre_fourMomentumOSData_osBasisPre]
  simp

@[simp]
lemma inner_fourMomentumOneParticlePre_osBasisPre (q : Fin 4 → ℝ) (A : OSConfig Unit) :
    ⟪fourMomentumOneParticlePre q, osBasisPre (fourMomentumOSData q) A⟫_ℂ =
      fourMomentumOddConfigTerm q A := by
  unfold fourMomentumOneParticlePre
  rw [inner_smul_left, inner_osBasisPre_fourMomentumOSData,
      fourMomentumEvenConfigTerm_osBaseConfig_one,
      fourMomentumOddConfigTerm_osBaseConfig_one]
  simp only [star_zero, zero_mul, zero_add, Complex.star_def, Complex.conj_ofReal]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, Complex.ofReal_one, one_mul]

@[simp]
lemma inner_osBasisPre_fourMomentumOneParticlePre (q : Fin 4 → ℝ) (A : OSConfig Unit) :
    ⟪osBasisPre (fourMomentumOSData q) A, fourMomentumOneParticlePre q⟫_ℂ =
      star (fourMomentumOddConfigTerm q A) := by
  rw [← inner_conj_symm, inner_fourMomentumOneParticlePre_osBasisPre, Complex.star_def]

@[simp]
lemma inner_osVacuumPre_fourMomentumOneParticlePre (q : Fin 4 → ℝ) :
    ⟪osVacuumPre (fourMomentumOSData q), fourMomentumOneParticlePre q⟫_ℂ = 0 := by
  unfold osVacuumPre
  rw [inner_osBasisPre_fourMomentumOneParticlePre]
  simp

@[simp]
lemma inner_fourMomentumOneParticlePre_osVacuumPre (q : Fin 4 → ℝ) :
    ⟪fourMomentumOneParticlePre q, osVacuumPre (fourMomentumOSData q)⟫_ℂ = 0 := by
  unfold osVacuumPre
  rw [inner_fourMomentumOneParticlePre_osBasisPre]
  simp

@[simp]
lemma inner_fourMomentumOneParticlePre_self (q : Fin 4 → ℝ) :
    ⟪fourMomentumOneParticlePre q, fourMomentumOneParticlePre q⟫_ℂ = 1 := by
  change ⟪fourMomentumOneParticlePre q,
    ((Real.exp (q 0) : ℝ) : ℂ) • osBasisPre (fourMomentumOSData q) (osBaseConfig 1)⟫_ℂ = 1
  rw [inner_smul_right, inner_fourMomentumOneParticlePre_osBasisPre,
      fourMomentumOddConfigTerm_osBaseConfig_one, ← Complex.ofReal_mul,
      ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]

@[simp]
theorem inner_osVacuum_fourMomentumOSData_self (q : Fin 4 → ℝ) :
    ⟪osVacuum (fourMomentumOSData q), osVacuum (fourMomentumOSData q)⟫_ℂ = 1 :=
  inner_osVacuum_self_of_normalized (fourMomentumOSData q) (fourMomentumS_vacuumNormalized q)

@[simp]
theorem norm_osVacuum_fourMomentumOSData (q : Fin 4 → ℝ) :
    ‖osVacuum (fourMomentumOSData q)‖ = 1 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_osVacuum_fourMomentumOSData_self]
  simp

@[simp]
theorem inner_osVacuum_fourMomentumOSData_osBasis (q : Fin 4 → ℝ) (A : OSConfig Unit) :
    ⟪osVacuum (fourMomentumOSData q), osBasis (fourMomentumOSData q) A⟫_ℂ =
      fourMomentumEvenConfigTerm q A := by
  dsimp [osVacuum, osBasis]
  rw [inner_toOSHilbert, inner_osVacuumPre_fourMomentumOSData_osBasisPre]

@[simp]
theorem inner_fourMomentumOneParticle_osBasis (q : Fin 4 → ℝ) (A : OSConfig Unit) :
    ⟪fourMomentumOneParticle q, osBasis (fourMomentumOSData q) A⟫_ℂ =
      fourMomentumOddConfigTerm q A := by
  dsimp [fourMomentumOneParticle, osBasis]
  rw [inner_toOSHilbert, inner_fourMomentumOneParticlePre_osBasisPre]

@[simp]
theorem inner_osVacuum_fourMomentumOneParticle (q : Fin 4 → ℝ) :
    ⟪osVacuum (fourMomentumOSData q), fourMomentumOneParticle q⟫_ℂ = 0 := by
  dsimp [osVacuum, fourMomentumOneParticle]
  rw [inner_toOSHilbert, inner_osVacuumPre_fourMomentumOneParticlePre]

@[simp]
theorem inner_fourMomentumOneParticle_osVacuum (q : Fin 4 → ℝ) :
    ⟪fourMomentumOneParticle q, osVacuum (fourMomentumOSData q)⟫_ℂ = 0 := by
  rw [← inner_conj_symm, inner_osVacuum_fourMomentumOneParticle, map_zero]

@[simp]
theorem inner_fourMomentumOneParticle_self (q : Fin 4 → ℝ) :
    ⟪fourMomentumOneParticle q, fourMomentumOneParticle q⟫_ℂ = 1 := by
  dsimp [fourMomentumOneParticle]
  rw [inner_toOSHilbert, inner_fourMomentumOneParticlePre_self]

@[simp]
theorem norm_fourMomentumOneParticle (q : Fin 4 → ℝ) :
    ‖fourMomentumOneParticle q‖ = 1 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_fourMomentumOneParticle_self]
  simp

theorem fourMomentumOneParticle_ne_zero (q : Fin 4 → ℝ) :
    fourMomentumOneParticle q ≠ 0 := by
  intro h
  have h1 := norm_fourMomentumOneParticle q
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

theorem osBasis_fourMomentumOSData_eq (q : Fin 4 → ℝ) (A : OSConfig Unit) :
    osBasis (fourMomentumOSData q) A =
      fourMomentumEvenConfigTerm q A • osVacuum (fourMomentumOSData q) +
        fourMomentumOddConfigTerm q A • fourMomentumOneParticle q := by
  let V : OSPreHilbertSpace (fourMomentumOSData q) :=
    fourMomentumEvenConfigTerm q A • osVacuumPre (fourMomentumOSData q) +
      fourMomentumOddConfigTerm q A • fourMomentumOneParticlePre q
  have h_AV : ⟪osBasisPre (fourMomentumOSData q) A, V⟫_ℂ =
      ⟪osBasisPre (fourMomentumOSData q) A, osBasisPre (fourMomentumOSData q) A⟫_ℂ := by
    change ⟪osBasisPre (fourMomentumOSData q) A,
      fourMomentumEvenConfigTerm q A • osVacuumPre (fourMomentumOSData q) +
        fourMomentumOddConfigTerm q A • fourMomentumOneParticlePre q⟫_ℂ = _
    rw [inner_add_right, inner_smul_right, inner_smul_right,
        inner_osBasisPre_osVacuumPre_fourMomentumOSData,
        inner_osBasisPre_fourMomentumOneParticlePre,
        inner_osBasisPre_fourMomentumOSData, mul_comm (fourMomentumEvenConfigTerm q A),
        mul_comm (fourMomentumOddConfigTerm q A)]
  have h_VA : ⟪V, osBasisPre (fourMomentumOSData q) A⟫_ℂ =
      ⟪osBasisPre (fourMomentumOSData q) A, osBasisPre (fourMomentumOSData q) A⟫_ℂ := by
    change ⟪fourMomentumEvenConfigTerm q A • osVacuumPre (fourMomentumOSData q) +
        fourMomentumOddConfigTerm q A • fourMomentumOneParticlePre q,
      osBasisPre (fourMomentumOSData q) A⟫_ℂ = _
    rw [inner_add_left, inner_smul_left, inner_smul_left,
        inner_osVacuumPre_fourMomentumOSData_osBasisPre,
        inner_fourMomentumOneParticlePre_osBasisPre,
        inner_osBasisPre_fourMomentumOSData]
    rfl
  have h_VV : ⟪V, V⟫_ℂ =
      ⟪osBasisPre (fourMomentumOSData q) A, osBasisPre (fourMomentumOSData q) A⟫_ℂ := by
    change ⟪fourMomentumEvenConfigTerm q A • osVacuumPre (fourMomentumOSData q) +
        fourMomentumOddConfigTerm q A • fourMomentumOneParticlePre q,
      fourMomentumEvenConfigTerm q A • osVacuumPre (fourMomentumOSData q) +
        fourMomentumOddConfigTerm q A • fourMomentumOneParticlePre q⟫_ℂ = _
    rw [inner_add_left, inner_add_right, inner_add_right,
        inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
        inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
        inner_osVacuumPre_fourMomentumOSData_self,
        inner_osVacuumPre_fourMomentumOneParticlePre,
        inner_fourMomentumOneParticlePre_osVacuumPre,
        inner_fourMomentumOneParticlePre_self,
        inner_osBasisPre_fourMomentumOSData]
    simp only [mul_one, mul_zero, add_zero, zero_add]
    rfl
  have h_sub : ‖osBasisPre (fourMomentumOSData q) A - V‖ = 0 := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_sub_left, inner_sub_right, inner_sub_right,
        h_AV, h_VA, h_VV, sub_self, map_zero, Real.sqrt_zero]
  have h_toV : toOSHilbert (fourMomentumOSData q) V =
      fourMomentumEvenConfigTerm q A • osVacuum (fourMomentumOSData q) +
        fourMomentumOddConfigTerm q A • fourMomentumOneParticle q := by
    dsimp [V, osVacuum, fourMomentumOneParticle]
    rw [map_add, (toOSHilbert (fourMomentumOSData q)).map_smul,
        (toOSHilbert (fourMomentumOSData q)).map_smul]
  rw [← h_toV, ← sub_eq_zero, ← norm_eq_zero]
  change ‖toOSHilbert (fourMomentumOSData q) (osBasisPre (fourMomentumOSData q) A) -
    toOSHilbert (fourMomentumOSData q) V‖ = 0
  rw [← map_sub, norm_toOSHilbert]
  exact h_sub

theorem fourMomentumHilbert_eq_vacuum_add_oneParticle (q : Fin 4 → ℝ)
    (Φ : OSHilbert (fourMomentumOSData q)) :
    Φ = ⟪osVacuum (fourMomentumOSData q), Φ⟫_ℂ • osVacuum (fourMomentumOSData q) +
        ⟪fourMomentumOneParticle q, Φ⟫_ℂ • fourMomentumOneParticle q := by
  have h_basis : ∀ A : OSConfig Unit,
      osBasis (fourMomentumOSData q) A =
        ⟪osVacuum (fourMomentumOSData q), osBasis (fourMomentumOSData q) A⟫_ℂ •
          osVacuum (fourMomentumOSData q) +
        ⟪fourMomentumOneParticle q, osBasis (fourMomentumOSData q) A⟫_ℂ •
          fourMomentumOneParticle q := by
    intro A
    rw [inner_osVacuum_fourMomentumOSData_osBasis,
        inner_fourMomentumOneParticle_osBasis]
    exact osBasis_fourMomentumOSData_eq q A
  induction Φ using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change toOSHilbert (fourMomentumOSData q) Ψ =
      ⟪osVacuum (fourMomentumOSData q), toOSHilbert (fourMomentumOSData q) Ψ⟫_ℂ •
        osVacuum (fourMomentumOSData q) +
      ⟪fourMomentumOneParticle q, toOSHilbert (fourMomentumOSData q) Ψ⟫_ℂ •
        fourMomentumOneParticle q
    have h_expand : toOSHilbert (fourMomentumOSData q) Ψ =
        ∑ A ∈ Ψ.toFinsupp.support, Ψ.toFinsupp A • osBasis (fourMomentumOSData q) A := by
      conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre (fourMomentumOSData q) Ψ]
      rw [map_finsuppSum]
      unfold Finsupp.sum
      refine Finset.sum_congr rfl (fun A _ => (toOSHilbert (fourMomentumOSData q)).map_smul _ _)
    rw [h_expand, inner_sum, inner_sum, Finset.sum_smul, Finset.sum_smul,
        ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    rw [inner_smul_right, inner_smul_right, mul_smul, mul_smul, ← smul_add, ← h_basis A]

noncomputable def fourMomentumHilbertLinearIsometryEquiv (q : Fin 4 → ℝ) :
    OSHilbert (fourMomentumOSData q) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  orthogonalTwoLinearIsometryEquiv
    (osVacuum (fourMomentumOSData q)) (fourMomentumOneParticle q)
    (inner_osVacuum_fourMomentumOSData_self q)
    (inner_osVacuum_fourMomentumOneParticle q)
    (inner_fourMomentumOneParticle_osVacuum q)
    (inner_fourMomentumOneParticle_self q)
    (norm_osVacuum_fourMomentumOSData q)
    (norm_fourMomentumOneParticle q)
    (fourMomentumHilbert_eq_vacuum_add_oneParticle q)

theorem osContractionSemigroup_fourMomentumOSData_osBasis
    {q : Fin 4 → ℝ} (hq0 : 0 ≤ q 0) (τ : ℝ) (hτ : 0 ≤ τ) (A : OSConfig Unit) :
    osContractionSemigroup (fourMomentumOSData q) (fourMomentumOSContraction hq0) τ hτ
      (osBasis (fourMomentumOSData q) A) =
      fourMomentumEvenConfigTerm q A • osVacuum (fourMomentumOSData q) +
        (fourMomentumOddConfigTerm q A * laplaceExp (q 0) (τ : ℂ)) •
          fourMomentumOneParticle q := by
  have h_shift :
      osContractionSemigroup (fourMomentumOSData q) (fourMomentumOSContraction hq0) τ hτ
        (osBasis (fourMomentumOSData q) A) =
      osBasis (fourMomentumOSData q) (osConfigTimeShift τ hτ A) := by
    dsimp [osBasis]
    rw [osContractionSemigroup_toOSHilbert]
    unfold osTimeShiftLM
    rw [osLiftConfigMap_osBasisPre]
  rw [h_shift, osBasis_fourMomentumOSData_eq,
      fourMomentumEvenConfigTerm_timeShift,
      fourMomentumOddConfigTerm_timeShift,
      laplaceExp_ofReal]
  have h_exp : -τ * q 0 = -(τ * q 0) := by ring
  rw [h_exp]

@[simp]
theorem osContractionSemigroup_fourMomentumOneParticle
    {q : Fin 4 → ℝ} (hq0 : 0 ≤ q 0) (τ : ℝ) (hτ : 0 ≤ τ) :
    osContractionSemigroup (fourMomentumOSData q) (fourMomentumOSContraction hq0) τ hτ
      (fourMomentumOneParticle q) =
      laplaceExp (q 0) (τ : ℂ) • fourMomentumOneParticle q := by
  conv_lhs => rw [fourMomentumOneParticle_eq_smul_osBasis q]
  rw [map_smul,
      osContractionSemigroup_fourMomentumOSData_osBasis hq0 τ hτ (osBaseConfig 1),
      fourMomentumEvenConfigTerm_osBaseConfig_one,
      fourMomentumOddConfigTerm_osBaseConfig_one,
      zero_smul, zero_add, smul_smul]
  congr 1
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, Complex.ofReal_one, one_mul]

theorem osContractionSemigroup_fourMomentumOSData_apply
    {q : Fin 4 → ℝ} (hq0 : 0 ≤ q 0) (τ : ℝ) (hτ : 0 ≤ τ)
    (Φ : OSHilbert (fourMomentumOSData q)) :
    osContractionSemigroup (fourMomentumOSData q) (fourMomentumOSContraction hq0) τ hτ Φ =
      ⟪osVacuum (fourMomentumOSData q), Φ⟫_ℂ • osVacuum (fourMomentumOSData q) +
        laplaceExp (q 0) (τ : ℂ) •
          (⟪fourMomentumOneParticle q, Φ⟫_ℂ • fourMomentumOneParticle q) := by
  conv_lhs => rw [fourMomentumHilbert_eq_vacuum_add_oneParticle q Φ]
  rw [map_add, map_smul, map_smul, osContractionSemigroup_vacuum,
      osContractionSemigroup_fourMomentumOneParticle hq0 τ hτ, smul_smul,
      mul_comm ⟪fourMomentumOneParticle q, Φ⟫_ℂ, ← smul_smul]

theorem osSpatialTranslate_fourMomentumOSData_osBasis
    (q : Fin 4 → ℝ) (htrans : OSTranslationInvariant (fourMomentumOSData q).𝒮)
    (a : Fin 3 → ℝ) (A : OSConfig Unit) :
    osSpatialTranslate (fourMomentumOSData q) htrans a (osBasis (fourMomentumOSData q) A) =
      fourMomentumEvenConfigTerm q A • osVacuum (fourMomentumOSData q) +
        (fourMomentumOddConfigTerm q A * fourMomentumSpatialPhase q a) •
          fourMomentumOneParticle q := by
  have h_shift :
      osSpatialTranslate (fourMomentumOSData q) htrans a (osBasis (fourMomentumOSData q) A) =
      osBasis (fourMomentumOSData q) (osConfigSpatialShift a A) := by
    dsimp [osBasis]
    rw [osSpatialTranslate_toOSHilbert]
    unfold osSpatialTranslateLM
    rw [osLiftConfigMap_osBasisPre]
  rw [h_shift, osBasis_fourMomentumOSData_eq,
      fourMomentumEvenConfigTerm_spatialShift,
      fourMomentumOddConfigTerm_spatialShift]

@[simp]
theorem osSpatialTranslate_fourMomentumOneParticle
    (q : Fin 4 → ℝ) (htrans : OSTranslationInvariant (fourMomentumOSData q).𝒮)
    (a : Fin 3 → ℝ) :
    osSpatialTranslate (fourMomentumOSData q) htrans a (fourMomentumOneParticle q) =
      fourMomentumSpatialPhase q a • fourMomentumOneParticle q := by
  conv_lhs => rw [fourMomentumOneParticle_eq_smul_osBasis q]
  rw [map_smul,
      osSpatialTranslate_fourMomentumOSData_osBasis q htrans a (osBaseConfig 1),
      fourMomentumEvenConfigTerm_osBaseConfig_one,
      fourMomentumOddConfigTerm_osBaseConfig_one,
      zero_smul, zero_add, smul_smul]
  congr 1
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, Complex.ofReal_one, one_mul]

theorem osSpatialTranslate_fourMomentumOSData_apply
    (q : Fin 4 → ℝ) (htrans : OSTranslationInvariant (fourMomentumOSData q).𝒮)
    (a : Fin 3 → ℝ) (Φ : OSHilbert (fourMomentumOSData q)) :
    osSpatialTranslate (fourMomentumOSData q) htrans a Φ =
      ⟪osVacuum (fourMomentumOSData q), Φ⟫_ℂ • osVacuum (fourMomentumOSData q) +
        fourMomentumSpatialPhase q a •
          (⟪fourMomentumOneParticle q, Φ⟫_ℂ • fourMomentumOneParticle q) := by
  conv_lhs => rw [fourMomentumHilbert_eq_vacuum_add_oneParticle q Φ]
  rw [map_add, map_smul, map_smul, osSpatialTranslate_vacuum,
      osSpatialTranslate_fourMomentumOneParticle q htrans a, smul_smul,
      mul_comm ⟪fourMomentumOneParticle q, Φ⟫_ℂ, ← smul_smul]

@[simp]
theorem inner_osVacuum_osSpatialTranslate_fourMomentumOSData
    (q : Fin 4 → ℝ) (htrans : OSTranslationInvariant (fourMomentumOSData q).𝒮)
    (a : Fin 3 → ℝ) (Φ : OSHilbert (fourMomentumOSData q)) :
    ⟪osVacuum (fourMomentumOSData q),
      osSpatialTranslate (fourMomentumOSData q) htrans a Φ⟫_ℂ =
    ⟪osVacuum (fourMomentumOSData q), Φ⟫_ℂ := by
  rw [osSpatialTranslate_fourMomentumOSData_apply, inner_add_right,
      inner_smul_right, inner_smul_right, inner_smul_right,
      inner_osVacuum_fourMomentumOSData_self,
      inner_osVacuum_fourMomentumOneParticle]
  simp

@[simp]
theorem inner_fourMomentumOneParticle_osSpatialTranslate
    (q : Fin 4 → ℝ) (htrans : OSTranslationInvariant (fourMomentumOSData q).𝒮)
    (a : Fin 3 → ℝ) (Φ : OSHilbert (fourMomentumOSData q)) :
    ⟪fourMomentumOneParticle q,
      osSpatialTranslate (fourMomentumOSData q) htrans a Φ⟫_ℂ =
    fourMomentumSpatialPhase q a * ⟪fourMomentumOneParticle q, Φ⟫_ℂ := by
  rw [osSpatialTranslate_fourMomentumOSData_apply, inner_add_right,
      inner_smul_right, inner_smul_right, inner_smul_right,
      inner_fourMomentumOneParticle_osVacuum,
      inner_fourMomentumOneParticle_self]
  simp

noncomputable def fourMomentumOSSpectralDecomposition
    {q : Fin 4 → ℝ} (hq0 : 0 ≤ q 0) :
    OSSpectralDecomposition (fourMomentumOSData q) (fourMomentumOSContraction hq0) 2 where
  E i := if i = 0 then 0 else q 0
  energy_nonneg i := by
    fin_cases i
    · exact le_rfl
    · exact hq0
  P i :=
    if i = 0 then
      rankOneProjCLM (osVacuum (fourMomentumOSData q))
    else
      rankOneProjCLM (fourMomentumOneParticle q)
  proj_selfAdjoint i x y := by
    fin_cases i <;> exact rankOneProjCLM_selfAdjoint _ x y
  proj_mul j k := by
    fin_cases j <;> fin_cases k
    · simp only [Fin.isValue, ↓reduceIte]
      exact rankOneProjCLM_comp_self (inner_osVacuum_fourMomentumOSData_self q)
    · simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, zero_ne_one, ↓reduceIte, one_ne_zero]
      exact rankOneProjCLM_comp_eq_zero_of_orth (inner_osVacuum_fourMomentumOneParticle q)
    · simp only [Fin.isValue, Fin.mk_one, one_ne_zero, ↓reduceIte, Fin.zero_eta]
      exact rankOneProjCLM_comp_eq_zero_of_orth (inner_fourMomentumOneParticle_osVacuum q)
    · simp only [Fin.isValue, Fin.mk_one, one_ne_zero, ↓reduceIte]
      exact rankOneProjCLM_comp_self (inner_fourMomentumOneParticle_self q)
  sum_proj x := by
    rw [Fin.sum_univ_two]
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    rw [if_pos rfl, if_neg h10, rankOneProjCLM_apply, rankOneProjCLM_apply]
    exact (fourMomentumHilbert_eq_vacuum_add_oneParticle q x).symm
  semigroup_eq τ hτ x := by
    rw [osContractionSemigroup_fourMomentumOSData_apply hq0 τ hτ x, Fin.sum_univ_two]
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    rw [if_pos rfl, if_pos rfl, if_neg h10, if_neg h10,
        laplaceExp_zero_left, one_smul, rankOneProjCLM_apply, rankOneProjCLM_apply]
  vacuum_eq z := by
    rw [Fin.sum_univ_two]
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    rw [if_pos rfl, if_pos rfl, if_neg h10, if_neg h10,
        laplaceExp_zero_left, one_smul, rankOneProjCLM_apply, rankOneProjCLM_apply,
        inner_osVacuum_fourMomentumOSData_self, inner_fourMomentumOneParticle_osVacuum,
        one_smul, zero_smul, smul_zero, add_zero]
  comm_spatial htrans a i := by
    ext x
    fin_cases i
    · simp only [Fin.isValue, Fin.zero_eta, ↓reduceIte, ContinuousLinearMap.comp_apply,
        rankOneProjCLM_apply, map_smul, osSpatialTranslate_vacuum,
        inner_osVacuum_osSpatialTranslate_fourMomentumOSData]
    · simp only [Fin.isValue, Fin.mk_one, one_ne_zero, ↓reduceIte,
        ContinuousLinearMap.comp_apply, rankOneProjCLM_apply, map_smul,
        osSpatialTranslate_fourMomentumOneParticle,
        inner_fourMomentumOneParticle_osSpatialTranslate, smul_smul, mul_comm]

noncomputable def fourMomentumOSHolomorphicSemigroup
    {q : Fin 4 → ℝ} (hq0 : 0 ≤ q 0) :
    OSHolomorphicSemigroup (fourMomentumOSData q) (fourMomentumOSContraction hq0) :=
  (fourMomentumOSSpectralDecomposition hq0).toOSHolomorphicSemigroup

noncomputable def fourMomentumOSSpectralMeasure
    {q : Fin 4 → ℝ} (hq0 : 0 ≤ q 0) :
    OSSpectralMeasure (fourMomentumOSData q) (fourMomentumOSContraction hq0) (Fin 2) :=
  (fourMomentumOSSpectralDecomposition hq0).toOSSpectralMeasure

@[simp]
theorem fourMomentumOSSpectralMeasure_twoPointTubePropagator_eq
    {q : Fin 4 → ℝ} (hq0 : 0 ≤ q 0)
    (htrans : OSTranslationInvariant (fourMomentumOSData q).𝒮)
    (Ψ Φ : OSHilbert (fourMomentumOSData q))
    (b : Fin 3 → ℝ) (z : Fin 2 → Fin 4 → ℂ) :
    (fourMomentumOSSpectralMeasure hq0).twoPointTubePropagator htrans Ψ Φ b z =
      (fourMomentumOSSpectralDecomposition hq0).twoPointTubePropagator htrans Ψ Φ b z :=
  (fourMomentumOSSpectralDecomposition hq0).toOSSpectralMeasure_twoPointTubePropagator
    htrans Ψ Φ b z

theorem fourMomentumOSSpectralMeasure_diag_zero_eq_discreteKallenLehmannTube
    {q : Fin 4 → ℝ} (hq0 : 0 ≤ q 0)
    (htrans : OSTranslationInvariant (fourMomentumOSData q).𝒮)
    (Ψ : OSHilbert (fourMomentumOSData q)) (z : Fin 2 → Fin 4 → ℂ) :
    (fourMomentumOSSpectralMeasure hq0).twoPointTubePropagator htrans Ψ Ψ 0 z =
      discreteKallenLehmannTube 2
        (fun a => ‖(fourMomentumOSSpectralMeasure hq0).P a Ψ‖ ^ 2)
        (fourMomentumOSSpectralMeasure hq0).E z := by
  rw [(fourMomentumOSSpectralMeasure
    hq0).twoPointTubePropagator_diag_zero_eq_measureKallenLehmannTube]
  exact measureKallenLehmannTube_count_eq_discreteKallenLehmannTube 2 _ _ z

theorem norm_fourMomentumOSSpectralMeasure_diag_zero_le_norm_sq
    {q : Fin 4 → ℝ} (hq0 : 0 ≤ q 0)
    (htrans : OSTranslationInvariant (fourMomentumOSData q).𝒮)
    (Ψ : OSHilbert (fourMomentumOSData q)) {z : Fin 2 → Fin 4 → ℂ}
    (hz : z ∈ forward_tube_n 2) :
    ‖(fourMomentumOSSpectralMeasure hq0).twoPointTubePropagator htrans Ψ Ψ 0 z‖ ≤ ‖Ψ‖ ^ 2 :=
  (fourMomentumOSSpectralMeasure hq0).norm_twoPointTubePropagator_diag_zero_le_norm_sq
    htrans Ψ hz

@[simp]
theorem fourMomentumOSSpectralDecomposition_twoPointTubePropagator_vacuum_eq_one
    {q : Fin 4 → ℝ} (hq0 : 0 ≤ q 0)
    (htrans : OSTranslationInvariant (fourMomentumOSData q).𝒮)
    (a : Fin 3 → ℝ) (z : Fin 2 → Fin 4 → ℂ) :
    (fourMomentumOSSpectralDecomposition hq0).twoPointTubePropagator htrans
      (osVacuum (fourMomentumOSData q)) (osVacuum (fourMomentumOSData q)) a z = 1 := by
  rw [(fourMomentumOSSpectralDecomposition hq0).twoPointTubePropagator_eq_sum_spectralTwoPointTube,
      Fin.sum_univ_two, osSpatialTranslate_vacuum]
  dsimp [fourMomentumOSSpectralDecomposition]
  rw [inner_osVacuum_fourMomentumOSData_self, inner_fourMomentumOneParticle_osVacuum,
      one_smul, zero_smul, inner_osVacuum_fourMomentumOSData_self, inner_zero_right,
      mul_one, mul_zero, add_zero]
  unfold spectralTwoPointTube
  exact laplaceExp_zero_left _

theorem fourMomentumOSSpectralDecomposition_twoPointTubePropagator_oneParticle_eq
    {q : Fin 4 → ℝ} (hq0 : 0 ≤ q 0)
    (htrans : OSTranslationInvariant (fourMomentumOSData q).𝒮)
    (a : Fin 3 → ℝ) (z : Fin 2 → Fin 4 → ℂ) :
    (fourMomentumOSSpectralDecomposition hq0).twoPointTubePropagator htrans
      (fourMomentumOneParticle q) (fourMomentumOneParticle q) a z =
      fourMomentumSpatialPhase q a * spectralTwoPointTube (q 0) z := by
  rw [(fourMomentumOSSpectralDecomposition hq0).twoPointTubePropagator_eq_sum_spectralTwoPointTube,
      Fin.sum_univ_two, osSpatialTranslate_fourMomentumOneParticle]
  dsimp [fourMomentumOSSpectralDecomposition]
  simp [mul_comm]

@[simp]
theorem fourMomentumOSSpectralDecomposition_twoPointTubePropagator_oneParticle_zero_eq
    {q : Fin 4 → ℝ} (hq0 : 0 ≤ q 0)
    (htrans : OSTranslationInvariant (fourMomentumOSData q).𝒮)
    (z : Fin 2 → Fin 4 → ℂ) :
    (fourMomentumOSSpectralDecomposition hq0).twoPointTubePropagator htrans
      (fourMomentumOneParticle q) (fourMomentumOneParticle q) 0 z =
      spectralTwoPointTube (q 0) z := by
  rw [fourMomentumOSSpectralDecomposition_twoPointTubePropagator_oneParticle_eq,
      fourMomentumSpatialPhase_zero, one_mul]

theorem fourMomentumOSSpectralDecomposition_twoPointTubePropagator_oneParticle_zero_eq_fourMomentumH
    {q : Fin 4 → ℝ} (hq0 : 0 ≤ q 0)
    (htrans : OSTranslationInvariant (fourMomentumOSData q).𝒮)
    (α : Fin 2 → Unit) (z : Fin 2 → Fin 4 → ℂ) :
    (fourMomentumOSSpectralDecomposition hq0).twoPointTubePropagator htrans
      (fourMomentumOneParticle q) (fourMomentumOneParticle q) 0 z =
      fourMomentumH (euclidTimeVec (q 0)) 2 α z := by
  rw [fourMomentumOSSpectralDecomposition_twoPointTubePropagator_oneParticle_zero_eq,
      fourMomentumH_two_euclidTimeVec]

lemma minkowskiInnerC_alternatingMomentum_euclidTimeVec
    (E : ℝ) (n : ℕ) (k : Fin n) (w : Fin 4 → ℂ) :
    minkowskiInnerC (fun μ => (alternatingMomentum n (euclidTimeVec E) k μ : ℂ)) w =
      (if k.val % 2 = 0 then (E : ℂ) else -(E : ℂ)) * w 0 := by
  dsimp [minkowskiInnerC, alternatingMomentum]
  by_cases hk : k.val % 2 = 0 <;> simp [euclidTimeVec, hk]

lemma minkowskiInnerC_neg_alternatingMomentum_euclidTimeVec
    (E : ℝ) (n : ℕ) (k : Fin n) (w : Fin 4 → ℂ) :
    minkowskiInnerC (fun μ => ((-alternatingMomentum n (euclidTimeVec E)) k μ : ℂ)) w =
      -(if k.val % 2 = 0 then (E : ℂ) else -(E : ℂ)) * w 0 := by
  dsimp [minkowskiInnerC, alternatingMomentum]
  by_cases hk : k.val % 2 = 0 <;> simp [euclidTimeVec, hk]

@[simp]
lemma wickEmbedN_euclidRotN_su2Conj_zero_coord
    (n : ℕ) (U : SU2) (x : Fin n → Fin 4 → ℝ) (k : Fin n) :
    wickEmbedN n (euclidRotN n U (su2Conj U) x) k 0 = wickEmbedN n x k 0 := by
  change ((euclidRotOfSU2 U (su2Conj U) *ᵥ x k) 0 : ℂ) * Complex.I =
    (x k 0 : ℂ) * Complex.I
  rw [euclidRotOfSU2_mulVec, euclidRotApply_su2Conj_time]

@[simp]
lemma vladimirov_kernel_wickEmbedN_euclidRotN_su2Conj_euclidTimeVec
    (E : ℝ) (n : ℕ) (U : SU2) (x : Fin n → Fin 4 → ℝ) :
    vladimirov_kernel n (wickEmbedN n (euclidRotN n U (su2Conj U) x))
      (alternatingMomentum n (euclidTimeVec E)) =
    vladimirov_kernel n (wickEmbedN n x)
      (alternatingMomentum n (euclidTimeVec E)) := by
  unfold vladimirov_kernel
  congr 2
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [minkowskiInnerC_alternatingMomentum_euclidTimeVec,
      minkowskiInnerC_alternatingMomentum_euclidTimeVec,
      wickEmbedN_euclidRotN_su2Conj_zero_coord]

@[simp]
lemma vladimirov_kernel_wickEmbedN_euclidRotN_su2Conj_neg_euclidTimeVec
    (E : ℝ) (n : ℕ) (U : SU2) (x : Fin n → Fin 4 → ℝ) :
    vladimirov_kernel n (wickEmbedN n (euclidRotN n U (su2Conj U) x))
      (-alternatingMomentum n (euclidTimeVec E)) =
    vladimirov_kernel n (wickEmbedN n x)
      (-alternatingMomentum n (euclidTimeVec E)) := by
  unfold vladimirov_kernel
  congr 2
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [minkowskiInnerC_neg_alternatingMomentum_euclidTimeVec,
      minkowskiInnerC_neg_alternatingMomentum_euclidTimeVec,
      wickEmbedN_euclidRotN_su2Conj_zero_coord]

@[simp]
theorem fourMomentumS_euclidTimeVec_euclidRotN_su2Conj
    (E : ℝ) (n : ℕ) (U : SU2) (α : Fin n → Unit) (x : Fin n → Fin 4 → ℝ) :
    fourMomentumS (euclidTimeVec E) n α (euclidRotN n U (su2Conj U) x) =
      fourMomentumS (euclidTimeVec E) n α x := by
  rw [fourMomentumS_apply, fourMomentumS_apply, fourMomentumH, fourMomentumH]
  split_ifs with hn
  · exact vladimirov_kernel_wickEmbedN_euclidRotN_su2Conj_euclidTimeVec E n U x
  · rfl

theorem fourMomentumS_euclidTimeVec_scalarRotInvariant (E : ℝ) :
    OSScalarRotInvariant (fourMomentumS (euclidTimeVec E)) :=
  fun n U α x _hx => fourMomentumS_euclidTimeVec_euclidRotN_su2Conj E n U α x

theorem fourMomentumS_euclidTimeVec_spinorRotCovariant (E : ℝ) :
    OSSpinorRotCovariant trivialRep (fourMomentumS (euclidTimeVec E)) := by
  intro n U α x _hx
  have h_prod :
      (∏ i : Fin n, osSpinorRotMatrix trivialRep U (α i) (α i)) = 1 :=
    Finset.prod_eq_one (fun i _ => rfl)
  rw [Fintype.sum_unique, h_prod, one_mul]
  exact fourMomentumS_euclidTimeVec_euclidRotN_su2Conj E n U α x

@[simp]
theorem fourMomentumEvenConfigTerm_pointRot_euclidTimeVec
    (E : ℝ) (U : SU2) (A : OSConfig Unit) :
    fourMomentumEvenConfigTerm (euclidTimeVec E) (osConfigPointRot U A) =
      fourMomentumEvenConfigTerm (euclidTimeVec E) A := by
  unfold fourMomentumEvenConfigTerm osConfigPointRot
  dsimp only
  split_ifs with hn
  · exact vladimirov_kernel_wickEmbedN_euclidRotN_su2Conj_euclidTimeVec E A.1 U A.2.2.val
  · rfl

@[simp]
theorem fourMomentumOddConfigTerm_pointRot_euclidTimeVec
    (E : ℝ) (U : SU2) (A : OSConfig Unit) :
    fourMomentumOddConfigTerm (euclidTimeVec E) (osConfigPointRot U A) =
      fourMomentumOddConfigTerm (euclidTimeVec E) A := by
  unfold fourMomentumOddConfigTerm osConfigPointRot
  dsimp only
  split_ifs with hn
  · exact vladimirov_kernel_wickEmbedN_euclidRotN_su2Conj_neg_euclidTimeVec E A.1 U A.2.2.val
  · rfl

@[simp]
theorem osBasis_pointRot_fourMomentumOSData_euclidTimeVec
    (E : ℝ) (U : SU2) (A : OSConfig Unit) :
    osBasis (fourMomentumOSData (euclidTimeVec E)) (osConfigPointRot U A) =
      osBasis (fourMomentumOSData (euclidTimeVec E)) A := by
  rw [osBasis_fourMomentumOSData_eq, osBasis_fourMomentumOSData_eq,
      fourMomentumEvenConfigTerm_pointRot_euclidTimeVec,
      fourMomentumOddConfigTerm_pointRot_euclidTimeVec]

@[simp]
theorem osSpatialRot_fourMomentumOSData_euclidTimeVec_eq_id
    (E : ℝ) (hrot : OSScalarRotInvariant (fourMomentumOSData (euclidTimeVec E)).𝒮)
    (U : SU2) :
    osSpatialRot (fourMomentumOSData (euclidTimeVec E)) hrot U =
      ContinuousLinearMap.id ℂ (OSHilbert (fourMomentumOSData (euclidTimeVec E))) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change osSpatialRot (fourMomentumOSData (euclidTimeVec E)) hrot U
      (toOSHilbert (fourMomentumOSData (euclidTimeVec E)) Ψ) =
      toOSHilbert (fourMomentumOSData (euclidTimeVec E)) Ψ
    rw [osSpatialRot_toOSHilbert]
    conv_lhs =>
      rw [osPreHilbert_eq_finsupp_sum_osBasisPre (fourMomentumOSData (euclidTimeVec E)) Ψ]
    conv_rhs =>
      rw [osPreHilbert_eq_finsupp_sum_osBasisPre (fourMomentumOSData (euclidTimeVec E)) Ψ]
    rw [map_finsuppSum, map_finsuppSum, map_finsuppSum]
    refine Finsupp.sum_congr (fun A _ => ?_)
    rw [LinearMap.map_smul,
        (toOSHilbert (fourMomentumOSData (euclidTimeVec E))).map_smul,
        (toOSHilbert (fourMomentumOSData (euclidTimeVec E))).map_smul]
    congr 1
    unfold osSpatialRotLM
    rw [osLiftConfigMap_osBasisPre]
    exact osBasis_pointRot_fourMomentumOSData_euclidTimeVec E U A

@[simp]
theorem osSpinorRot_fourMomentumOSData_euclidTimeVec_eq_id
    (E : ℝ)
    (hrot : OSSpinorRotCovariant trivialRep (fourMomentumOSData (euclidTimeVec E)).𝒮)
    (U : SU2) :
    osSpinorRot (fourMomentumOSData (euclidTimeVec E)) hrot U =
      ContinuousLinearMap.id ℂ (OSHilbert (fourMomentumOSData (euclidTimeVec E))) := by
  have hU : osSpinorRotMatrix trivialRep U⁻¹ = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  rw [osSpinorRot_eq_osSpatialRot_of_matrix_eq_one (fourMomentumOSData (euclidTimeVec E))
      hrot (fourMomentumS_euclidTimeVec_scalarRotInvariant E) U hU]
  exact osSpatialRot_fourMomentumOSData_euclidTimeVec_eq_id E
    (fourMomentumS_euclidTimeVec_scalarRotInvariant E) U

def diagImagSU2 : SU2 :=
  ⟨diagImagMatrix, by
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    refine ⟨?_, by unfold diagImagMatrix; rw [Matrix.det_fin_two_of]; simp⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagImagMatrix, Matrix.mul_apply, Fin.sum_univ_two]⟩

def symplecticSU2 : SU2 :=
  ⟨symplecticMatrix, by
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    refine ⟨?_, by unfold symplecticMatrix; rw [Matrix.det_fin_two_of]; ring⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [symplecticMatrix, Matrix.mul_apply, Fin.sum_univ_two]⟩

lemma vec_to_spinor_injective : Function.Injective vec_to_spinor :=
  Function.LeftInverse.injective spinor_to_vec_left_inv

lemma euclidRotApply_diagImagSU2 (y : Fin 4 → ℝ) :
    euclidRotApply diagImagSU2 (su2Conj diagImagSU2) y = ![y 0, -y 1, -y 2, y 3] := by
  apply wickEmbed_injective
  rw [wickEmbed_euclidRotApply]
  apply vec_to_spinor_injective
  change vec_to_spinor
    (spinorPhi_matrix (su2ToSL2C diagImagSU2) (su2ToSL2C (su2Conj diagImagSU2)) *ᵥ
      wickEmbed y) = _
  rw [spinorPhi_matrix_mulVec]
  simp only [spinor_action, vec_to_spinor_right_inv, su2ToSL2C, su2Conj_val_transpose]
  have hinv : (diagImagSU2⁻¹).val = -diagImagMatrix := by
    change star diagImagMatrix = -diagImagMatrix
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagImagMatrix]
  change diagImagMatrix * vec_to_spinor (wickEmbed y) * (diagImagSU2⁻¹).val = _
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [diagImagMatrix, vec_to_spinor, wickEmbed, Matrix.mul_apply,
        Matrix.vecMul, dotProduct, Fin.sum_univ_two]
      ring_nf
      simp
      ring

lemma euclidRotApply_symplecticSU2 (y : Fin 4 → ℝ) :
    euclidRotApply symplecticSU2 (su2Conj symplecticSU2) y = ![y 0, -y 1, y 2, -y 3] := by
  apply wickEmbed_injective
  rw [wickEmbed_euclidRotApply]
  apply vec_to_spinor_injective
  change vec_to_spinor
    (spinorPhi_matrix (su2ToSL2C symplecticSU2) (su2ToSL2C (su2Conj symplecticSU2)) *ᵥ
      wickEmbed y) = _
  rw [spinorPhi_matrix_mulVec]
  simp only [spinor_action, vec_to_spinor_right_inv, su2ToSL2C, su2Conj_val_transpose]
  have hinv : (symplecticSU2⁻¹).val = -symplecticMatrix := by
    change star symplecticMatrix = -symplecticMatrix
    ext i j
    fin_cases i <;> fin_cases j <;> simp [symplecticMatrix]
  change symplecticMatrix * vec_to_spinor (wickEmbed y) * (symplecticSU2⁻¹).val = _
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [symplecticMatrix, vec_to_spinor, wickEmbed, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two]; try ring)

def euclidTwoPointSpatial (v : Fin 3 → ℝ) : Fin 2 → Fin 4 → ℝ :=
  fun i => if i = 0 then 0 else ![1, v 0, v 1, v 2]

lemma euclidTwoPointSpatial_mem_orderedEuclidN (v : Fin 3 → ℝ) :
    euclidTwoPointSpatial v ∈ orderedEuclidN 2 := by
  intro i hi
  have hi0 : i = 0 := Fin.ext (by omega)
  subst hi0
  simp [euclidTwoPointSpatial]

lemma euclidRotN_diagImagSU2_euclidTwoPointSpatial (v : Fin 3 → ℝ) :
    euclidRotN 2 diagImagSU2 (su2Conj diagImagSU2) (euclidTwoPointSpatial v) =
      euclidTwoPointSpatial ![-v 0, -v 1, v 2] := by
  ext i μ
  change (euclidRotOfSU2 diagImagSU2 (su2Conj diagImagSU2) *ᵥ euclidTwoPointSpatial v i) μ =
    euclidTwoPointSpatial ![-v 0, -v 1, v 2] i μ
  rw [euclidRotOfSU2_mulVec, euclidRotApply_diagImagSU2]
  fin_cases i <;> fin_cases μ <;> simp [euclidTwoPointSpatial]

lemma euclidRotN_symplecticSU2_euclidTwoPointSpatial (v : Fin 3 → ℝ) :
    euclidRotN 2 symplecticSU2 (su2Conj symplecticSU2) (euclidTwoPointSpatial v) =
      euclidTwoPointSpatial ![-v 0, v 1, -v 2] := by
  ext i μ
  change (euclidRotOfSU2 symplecticSU2 (su2Conj symplecticSU2) *ᵥ euclidTwoPointSpatial v i) μ =
    euclidTwoPointSpatial ![-v 0, v 1, -v 2] i μ
  rw [euclidRotOfSU2_mulVec, euclidRotApply_symplecticSU2]
  fin_cases i <;> fin_cases μ <;> simp [euclidTwoPointSpatial]

lemma fourMomentumS_two_euclidTwoPointSpatial (q : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    fourMomentumS q 2 default (euclidTwoPointSpatial v) =
      Complex.exp (-(q 0 : ℂ) -
        Complex.I * ((q 1 * v 0 + q 2 * v 1 + q 3 * v 2 : ℝ) : ℂ)) := by
  rw [fourMomentumS_apply, fourMomentumH, if_pos rfl]
  unfold vladimirov_kernel
  rw [Fin.sum_univ_two]
  congr 1
  have h0 : alternatingMomentum 2 q 0 = q := by simp [alternatingMomentum]
  have h1 : alternatingMomentum 2 q 1 = -q := by simp [alternatingMomentum]
  rw [h0, h1]
  simp [minkowskiInnerC, wickEmbed, euclidTwoPointSpatial]
  linear_combination (q 0 : ℂ) * Complex.I_sq

lemma eq_zero_of_exp_neg_q0_phase_neg_eq (a b : ℝ)
    (h : ∀ t : ℝ,
      Complex.exp (-(a : ℂ) - Complex.I * ((-(b * t) : ℝ) : ℂ)) =
        Complex.exp (-(a : ℂ) - Complex.I * ((b * t : ℝ) : ℂ))) :
    b = 0 := by
  by_contra hb
  have ht := h (Real.pi / (2 * b))
  have hbt : b * (Real.pi / (2 * b)) = Real.pi / 2 := by field_simp
  rw [hbt] at ht
  have h_fac1 : -(a : ℂ) - Complex.I * ((-(Real.pi / 2) : ℝ) : ℂ) =
      -(a : ℂ) + ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have h_fac2 : -(a : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ) =
      -(a : ℂ) + ((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h_fac1, h_fac2, Complex.exp_add, Complex.exp_add] at ht
  have h_cancel := mul_left_cancel₀ (Complex.exp_ne_zero (-(a : ℂ))) ht
  have h_im := congrArg Complex.im h_cancel
  rw [Complex.exp_mul_I, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin] at h_im
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, mul_zero, Complex.I_im, mul_one, add_zero, zero_add,
    Real.sin_neg, Real.sin_pi_div_two] at h_im
  linarith

theorem osScalarRotInvariant_fourMomentumS_iff (q : Fin 4 → ℝ) :
    OSScalarRotInvariant (fourMomentumS q) ↔ q = euclidTimeVec (q 0) := by
  refine ⟨fun hrot => ?_, fun hq => ?_⟩
  · have h1 : q 1 = 0 := by
      refine eq_zero_of_exp_neg_q0_phase_neg_eq (q 0) (q 1) (fun t => ?_)
      have h_eq := hrot 2 diagImagSU2 default (euclidTwoPointSpatial ![t, 0, 0])
        (euclidTwoPointSpatial_mem_orderedEuclidN ![t, 0, 0])
      rw [euclidRotN_diagImagSU2_euclidTwoPointSpatial,
          fourMomentumS_two_euclidTwoPointSpatial,
          fourMomentumS_two_euclidTwoPointSpatial] at h_eq
      simpa using h_eq
    have h2 : q 2 = 0 := by
      refine eq_zero_of_exp_neg_q0_phase_neg_eq (q 0) (q 2) (fun t => ?_)
      have h_eq := hrot 2 diagImagSU2 default (euclidTwoPointSpatial ![0, t, 0])
        (euclidTwoPointSpatial_mem_orderedEuclidN ![0, t, 0])
      rw [euclidRotN_diagImagSU2_euclidTwoPointSpatial,
          fourMomentumS_two_euclidTwoPointSpatial,
          fourMomentumS_two_euclidTwoPointSpatial] at h_eq
      simpa using h_eq
    have h3 : q 3 = 0 := by
      refine eq_zero_of_exp_neg_q0_phase_neg_eq (q 0) (q 3) (fun t => ?_)
      have h_eq := hrot 2 symplecticSU2 default (euclidTwoPointSpatial ![0, 0, t])
        (euclidTwoPointSpatial_mem_orderedEuclidN ![0, 0, t])
      rw [euclidRotN_symplecticSU2_euclidTwoPointSpatial,
          fourMomentumS_two_euclidTwoPointSpatial,
          fourMomentumS_two_euclidTwoPointSpatial] at h_eq
      simpa using h_eq
    ext μ
    fin_cases μ <;> simp [euclidTimeVec, h1, h2, h3]
  · rw [hq]
    exact fourMomentumS_euclidTimeVec_scalarRotInvariant (q 0)

theorem osSpinorRotCovariant_fourMomentumS_iff (q : Fin 4 → ℝ) :
    OSSpinorRotCovariant trivialRep (fourMomentumS q) ↔ q = euclidTimeVec (q 0) := by
  refine ⟨fun hrot => (osScalarRotInvariant_fourMomentumS_iff q).mp ?_, fun hq => ?_⟩
  · intro n U α x hx
    have h_eq := hrot n U α x hx
    have h_prod :
        (∏ i : Fin n, osSpinorRotMatrix trivialRep U (α i) (α i)) = 1 :=
      Finset.prod_eq_one (fun i _ => rfl)
    rw [Fintype.sum_unique, h_prod, one_mul] at h_eq
    exact h_eq
  · rw [hq]
    exact fourMomentumS_euclidTimeVec_spinorRotCovariant (q 0)

theorem not_osScalarRotInvariant_sampleFourMomentum :
    ¬ OSScalarRotInvariant (fourMomentumS sampleFourMomentum) := by
  rw [osScalarRotInvariant_fourMomentumS_iff]
  intro h
  have h1 := congr_fun h 1
  simp [sampleFourMomentum, euclidTimeVec] at h1

theorem not_osSpinorRotCovariant_sampleFourMomentum :
    ¬ OSSpinorRotCovariant trivialRep (fourMomentumS sampleFourMomentum) := by
  rw [osSpinorRotCovariant_fourMomentumS_iff]
  intro h
  have h1 := congr_fun h 1
  simp [sampleFourMomentum, euclidTimeVec] at h1

theorem not_euclidRotCovariant_fourMomentumS
    {q : Fin 4 → ℝ} (hq : q ≠ 0) :
    ¬ EuclidRotCovariant trivialRep (fourMomentumS q) := by
  intro hrot
  by_cases hq0 : q 0 = 0
  · have h_vec := (osSpinorRotCovariant_fourMomentumS_iff q).mp hrot.osSpinorRotCovariant
    rw [hq0, euclidTimeVec_zero] at h_vec
    exact hq h_vec
  · exact not_euclidRotCovariant_fourMomentumS_of_zero_apply_ne_zero hq0 hrot

theorem not_osAxioms_fourMomentumS
    {q : Fin 4 → ℝ} (hq : q ≠ 0) (η : ℂ) :
    ¬ OSAxioms trivialRep trivialStarStructure η (fourMomentumS q) :=
  fun hOS => not_euclidRotCovariant_fourMomentumS hq hOS.os1_rotation

theorem not_tubeCovariant_fourMomentumTubeExtension
    {q : Fin 4 → ℝ} (hq : q ≠ 0) :
    ¬ TubeCovariant trivialRep (fourMomentumTubeExtension q) :=
  fun hcov => not_euclidRotCovariant_fourMomentumS hq
    (schwingerFromTube_euclidCovariant trivialRep (fourMomentumW q)
      (fourMomentumTubeExtension q) hcov)

theorem not_tubeCovariant_sampleFourMomentum :
    ¬ TubeCovariant trivialRep (fourMomentumTubeExtension sampleFourMomentum) :=
  not_tubeCovariant_fourMomentumTubeExtension sampleFourMomentum_ne_zero

lemma inner_osTimeShiftLM_fourMomentumOneParticlePre_self
    (q : Fin 4 → ℝ) (τ : ℝ) (hτ : 0 ≤ τ) :
    ⟪osTimeShiftLM (fourMomentumOSData q) τ hτ (fourMomentumOneParticlePre q),
      osTimeShiftLM (fourMomentumOSData q) τ hτ (fourMomentumOneParticlePre q)⟫_ℂ =
    ((Real.exp (-(2 * τ * q 0)) : ℝ) : ℂ) := by
  unfold fourMomentumOneParticlePre osTimeShiftLM
  rw [map_smul, osLiftConfigMap_osBasisPre, inner_smul_left, inner_smul_right,
      inner_osBasisPre_fourMomentumOSData,
      fourMomentumEvenConfigTerm_timeShift,
      fourMomentumOddConfigTerm_timeShift,
      fourMomentumEvenConfigTerm_osBaseConfig_one,
      fourMomentumOddConfigTerm_osBaseConfig_one]
  simp only [star_zero, zero_mul, zero_add, Complex.star_def,
    Complex.conj_ofReal, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 1
  congr 1
  ring

lemma norm_osTimeShiftLM_fourMomentumOneParticlePre
    (q : Fin 4 → ℝ) (τ : ℝ) (hτ : 0 ≤ τ) :
    ‖osTimeShiftLM (fourMomentumOSData q) τ hτ (fourMomentumOneParticlePre q)‖ =
      Real.exp (-(τ * q 0)) := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_osTimeShiftLM_fourMomentumOneParticlePre_self]
  change Real.sqrt (Real.exp (-(2 * τ * q 0))) = Real.exp (-(τ * q 0))
  have h_sq : Real.exp (-(2 * τ * q 0)) = Real.exp (-(τ * q 0)) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [h_sq, Real.sqrt_sq (Real.exp_pos _).le]

theorem osContractionCondition_fourMomentumOSData_iff (q : Fin 4 → ℝ) :
    OSContractionCondition (fourMomentumOSData q) ↔ 0 ≤ q 0 := by
  refine ⟨fun hcontr => ?_, fourMomentumOSContraction⟩
  have h1 := hcontr 1 zero_le_one (fourMomentumOneParticlePre q)
  have h_norm0 : ‖fourMomentumOneParticlePre q‖ = 1 := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_fourMomentumOneParticlePre_self]
    simp
  rw [norm_osTimeShiftLM_fourMomentumOneParticlePre, h_norm0, Real.exp_le_one_iff] at h1
  linarith

theorem osDiagonalKernelBounded_fourMomentumS_iff (q : Fin 4 → ℝ) :
    OSDiagonalKernelBounded trivialStarStructure (fourMomentumS q) ↔ 0 ≤ q 0 := by
  refine ⟨fun hdiag => ?_, fourMomentumOSDiagonalKernelBounded⟩
  exact (osContractionCondition_fourMomentumOSData_iff q).mp
    (osContractionCondition_of_diagonalKernelBounded (fourMomentumOSData q)
      (fourMomentumOSTranslationInvariant q) hdiag)

theorem osTimeClusterDecomposition_fourMomentumOSData_iff (q : Fin 4 → ℝ) :
    OSTimeClusterDecomposition (fourMomentumOSData q) ↔ 0 < q 0 := by
  refine ⟨fun hcluster => ?_, fourMomentumOSTimeCluster⟩
  have hcontr : OSContractionCondition (fourMomentumOSData q) :=
    osContractionCondition_of_timeCluster (fourMomentumOSData q)
      (fourMomentumOSTranslationInvariant q) hcluster
  have hq0 : 0 ≤ q 0 := (osContractionCondition_fourMomentumOSData_iff q).mp hcontr
  refine lt_of_le_of_ne hq0 (fun h0 => ?_)
  have h_fixed : ∀ (τ : ℝ) (hτ : 0 ≤ τ),
      osContractionSemigroup (fourMomentumOSData q) (fourMomentumOSContraction hq0) τ hτ
        (fourMomentumOneParticle q) = fourMomentumOneParticle q := by
    intro τ hτ
    rw [osContractionSemigroup_fourMomentumOneParticle hq0 τ hτ, ← h0,
        laplaceExp_zero_left, one_smul]
  have h_eq := eq_smul_osVacuum_of_osContractionSemigroup_fixed
    (fourMomentumOSData q) (fourMomentumOSContraction hq0) hcluster h_fixed
  rw [inner_osVacuum_fourMomentumOneParticle, zero_smul] at h_eq
  exact fourMomentumOneParticle_ne_zero q h_eq

lemma zero_apply_nonneg_of_mem_closed_forward_light_cone
    {q : Fin 4 → ℝ} (hq : q ∈ closed_forward_light_cone) :
    0 ≤ q 0 :=
  hq.1

lemma zero_apply_nonneg_of_mem_closure_forward_light_cone
    {q : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone) :
    0 ≤ q 0 :=
  zero_apply_nonneg_of_mem_closed_forward_light_cone
    (closure_forward_light_cone_subset hq)

lemma zero_apply_pos_of_mem_closed_forward_light_cone
    {q : Fin 4 → ℝ} (hq : q ∈ closed_forward_light_cone) (hne : q ≠ 0) :
    0 < q 0 :=
  lt_of_le_of_ne (zero_apply_nonneg_of_mem_closed_forward_light_cone hq)
    (zero_apply_ne_zero_of_mem_closed_forward_light_cone hq hne).symm

lemma zero_apply_pos_of_mem_closure_forward_light_cone
    {q : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone) (hne : q ≠ 0) :
    0 < q 0 :=
  zero_apply_pos_of_mem_closed_forward_light_cone
    (closure_forward_light_cone_subset hq) hne

theorem fourMomentumOSDiagonalKernelBounded_of_mem_closure_forward_light_cone
    {q : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone) :
    OSDiagonalKernelBounded trivialStarStructure (fourMomentumS q) :=
  fourMomentumOSDiagonalKernelBounded
    (zero_apply_nonneg_of_mem_closure_forward_light_cone hq)

theorem fourMomentumOSContraction_of_mem_closure_forward_light_cone
    {q : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone) :
    OSContractionCondition (fourMomentumOSData q) :=
  fourMomentumOSContraction
    (zero_apply_nonneg_of_mem_closure_forward_light_cone hq)

noncomputable def fourMomentumOSSpectralDecomposition_of_mem_closure_forward_light_cone
    {q : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone) :
    OSSpectralDecomposition (fourMomentumOSData q)
      (fourMomentumOSContraction_of_mem_closure_forward_light_cone hq) 2 :=
  fourMomentumOSSpectralDecomposition
    (zero_apply_nonneg_of_mem_closure_forward_light_cone hq)

noncomputable def fourMomentumOSHolomorphicSemigroup_of_mem_closure_forward_light_cone
    {q : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone) :
    OSHolomorphicSemigroup (fourMomentumOSData q)
      (fourMomentumOSContraction_of_mem_closure_forward_light_cone hq) :=
  fourMomentumOSHolomorphicSemigroup
    (zero_apply_nonneg_of_mem_closure_forward_light_cone hq)

noncomputable def fourMomentumOSSpectralMeasure_of_mem_closure_forward_light_cone
    {q : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone) :
    OSSpectralMeasure (fourMomentumOSData q)
      (fourMomentumOSContraction_of_mem_closure_forward_light_cone hq) (Fin 2) :=
  fourMomentumOSSpectralMeasure
    (zero_apply_nonneg_of_mem_closure_forward_light_cone hq)

theorem fourMomentumOSTimeCluster_of_mem_closure_forward_light_cone
    {q : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone) (hne : q ≠ 0) :
    OSTimeClusterDecomposition (fourMomentumOSData q) :=
  fourMomentumOSTimeCluster
    (zero_apply_pos_of_mem_closure_forward_light_cone hq hne)

theorem minkowskiFourier_comp_rev (n : ℕ)
    (f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hf' : ∀ x : Fin n → Fin 4 → ℝ, f' (fun i => x (Fin.rev i)) = f x)
    (p : Fin n → Fin 4 → ℝ) :
    minkowskiFourier f p = minkowskiFourier f' (fun i => p (Fin.rev i)) := by
  unfold minkowskiFourier
  rw [← integral_comp_rev n (fun x : Fin n → Fin 4 → ℝ =>
    f' x * Complex.exp (-(Complex.I *
      ((∑ i : Fin n, minkowskiInner (p (Fin.rev i)) (x i) : ℝ) : ℂ))))]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  dsimp only
  have h_sum : (∑ k : Fin n, minkowskiInner (p k) (x k)) =
      ∑ i : Fin n, minkowskiInner (p (Fin.rev i)) (x (Fin.rev i)) :=
    (Equiv.sum_comp Fin.revPerm
      (fun i : Fin n => minkowskiInner (p i) (x i))).symm
  rw [hf' x, h_sum]

theorem fourMomentumW_rev_eq_neg (q : Fin 4 → ℝ) (n : ℕ) (α : Fin n → Unit)
    (f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hf' : ∀ x : Fin n → Fin 4 → ℝ, f' (fun i => x (Fin.rev i)) = f x) :
    fourMomentumW q n α f = fourMomentumW (-q) n (α ∘ Fin.rev) f' := by
  rw [fourMomentumW_apply, fourMomentumW_apply]
  by_cases hn : n % 2 = 0
  · rw [if_pos hn, if_pos hn, minkowskiFourier_comp_rev n f f' hf']
    congr 1
    ext i μ
    rw [alternatingMomentum_rev_of_even n hn q i, alternatingMomentum_neg]
    rfl
  · simp [hn]

theorem fourMomentumH_rev_eq_neg (q : Fin 4 → ℝ) (n : ℕ) (α : Fin n → Unit)
    (z : Fin n → Fin 4 → ℂ) :
    fourMomentumH q n α (z ∘ Fin.rev) = fourMomentumH (-q) n (α ∘ Fin.rev) z := by
  unfold fourMomentumH
  by_cases hn : n % 2 = 0
  · rw [if_pos hn, if_pos hn]
    unfold vladimirov_kernel
    congr 1
    rw [← Equiv.sum_comp Fin.revPerm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h_rev : Fin.revPerm i = Fin.rev i := rfl
    have h_z : (z ∘ Fin.rev) (Fin.rev i) = z i := by
      change z (Fin.rev (Fin.rev i)) = z i
      rw [Fin.rev_rev]
    have h_p : alternatingMomentum n q (Fin.rev i) = alternatingMomentum n (-q) i := by
      rw [alternatingMomentum_rev_of_even n hn q i, alternatingMomentum_neg]
      rfl
    rw [h_rev, h_z, h_p]
  · simp [hn]

theorem fourMomentumW_translationInvariant (q : Fin 4 → ℝ)
    (n : ℕ) (α : Fin n → Unit) (a : Fin 4 → ℝ)
    (f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hf' : ∀ x : Fin n → Fin 4 → ℝ, f' (fun i => x i + a) = f x) :
    fourMomentumW q n α f' = fourMomentumW q n α f :=
  wightman_translationInvariant_of_tubeTranslationInvariant
    (fourMomentumTubeExtension q) (fourMomentumTubeTranslationInvariant q) n α a f f' hf'

theorem fourMomentumWeakLocality_zero :
    WeakLocality 1 (fourMomentumW 0) := by
  intro n α f f' _hf_jost hf'
  rw [one_pow, one_mul, fourMomentumW_rev_eq_neg 0 n α f f' hf', neg_zero]

@[simp]
lemma alternatingMomentum_zero_momentum (n : ℕ) :
    alternatingMomentum n 0 = 0 := by
  ext i μ
  dsimp [alternatingMomentum]
  split_ifs <;> simp

@[simp]
theorem fourMomentumH_zero_momentum_eq (n : ℕ) (α : Fin n → Unit)
    (z : Fin n → Fin 4 → ℂ) :
    fourMomentumH 0 n α z = z2FreeCoeff n := by
  unfold fourMomentumH vladimirov_kernel
  rw [z2FreeCoeff_eq_ite]
  by_cases hn : n % 2 = 0
  · rw [if_pos hn, if_pos hn, alternatingMomentum_zero_momentum]
    simp [minkowskiInnerC]
  · simp [hn]

@[simp]
theorem fourMomentumS_zero_momentum_eq :
    fourMomentumS 0 = z2FreeS := by
  ext n α x
  rw [fourMomentumS_apply, fourMomentumH_zero_momentum_eq]
  rfl

@[simp]
theorem fourMomentumW_zero_momentum_eq :
    fourMomentumW 0 = z2FreeW := by
  ext n α f
  unfold z2FreeW
  rw [fourMomentumW_apply, momentW_apply, z2FreeCoeff_eq_ite]
  by_cases hn : n % 2 = 0
  · rw [if_pos hn, if_pos hn, one_mul, alternatingMomentum_zero_momentum,
        minkowskiFourier_eval_zero_n]
  · simp [hn]

theorem zeroMomentumSpectrumCondition_fourMomentumW_iff (q : Fin 4 → ℝ) :
    ZeroMomentumSpectrumCondition (fourMomentumW q) ↔ q = 0 := by
  refine ⟨fun hspec => ?_, fun h0 => ?_⟩
  · by_contra hne
    exact not_zeroMomentumSpectrumCondition_fourMomentumW hne hspec
  · subst h0
    rw [fourMomentumW_zero_momentum_eq]
    exact momentZeroMomentumSpectrumCondition z2FreeCoeff

theorem euclidRotCovariant_fourMomentumS_iff (q : Fin 4 → ℝ) :
    EuclidRotCovariant trivialRep (fourMomentumS q) ↔ q = 0 := by
  refine ⟨fun hrot => ?_, fun h0 => ?_⟩
  · by_contra hne
    exact not_euclidRotCovariant_fourMomentumS hne hrot
  · subst h0
    rw [fourMomentumS_zero_momentum_eq]
    exact z2FreeOSReconstructedWightman.osAxioms.os1_rotation

theorem tubeCovariant_fourMomentumTubeExtension_iff (q : Fin 4 → ℝ) :
    TubeCovariant trivialRep (fourMomentumTubeExtension q) ↔ q = 0 := by
  refine ⟨fun hcov => ?_, fun h0 => ?_⟩
  · by_contra hne
    exact not_tubeCovariant_fourMomentumTubeExtension hne hcov
  · subst h0
    intro n A z hz hAz α
    change fourMomentumH 0 n α (spinorPhi (A, sl2c_conj A) • z) = _
    rw [fourMomentumH_zero_momentum_eq]
    have h_rhs := momentTubeCovariant z2FreeCoeff n A z hz hAz α
    simpa [momentTubeExtension, momentH, fourMomentumH_zero_momentum_eq] using h_rhs

theorem osAxioms_one_fourMomentumS_iff (q : Fin 4 → ℝ) :
    OSAxioms trivialRep trivialStarStructure 1 (fourMomentumS q) ↔ q = 0 := by
  refine ⟨fun hOS => ?_, fun h0 => ?_⟩
  · by_contra hne
    exact not_osAxioms_fourMomentumS hne 1 hOS
  · subst h0
    rw [fourMomentumS_zero_momentum_eq]
    exact z2FreeOSReconstructedWightman.osAxioms

noncomputable def fourMomentumZeroEuclideanTubeBridge :
    OSEuclideanTubeBridge trivialRep trivialStarStructure 1 (fourMomentumS 0) :=
  Eq.mp (congrArg (OSEuclideanTubeBridge trivialRep trivialStarStructure 1)
    fourMomentumS_zero_momentum_eq.symm) z2FreeEuclideanTubeBridgeOfOSData

theorem eqMp_osEuclideanTubeBridge_W {s t : SchwingerFamily Unit} (h : s = t)
    (B : OSEuclideanTubeBridge trivialRep trivialStarStructure 1 s) :
    (Eq.mp (congrArg (OSEuclideanTubeBridge trivialRep trivialStarStructure 1) h) B).W = B.W := by
  subst h
  rfl

theorem eqMp_osEuclideanTubeBridge_E_H {s t : SchwingerFamily Unit} (h : s = t)
    (B : OSEuclideanTubeBridge trivialRep trivialStarStructure 1 s) :
    (Eq.mp (congrArg (OSEuclideanTubeBridge trivialRep trivialStarStructure 1) h) B).E.H =
      B.E.H := by
  subst h
  rfl

@[simp]
theorem fourMomentumZeroEuclideanTubeBridge_W :
    fourMomentumZeroEuclideanTubeBridge.W = fourMomentumW 0 := by
  unfold fourMomentumZeroEuclideanTubeBridge
  rw [eqMp_osEuclideanTubeBridge_W fourMomentumS_zero_momentum_eq.symm]
  exact fourMomentumW_zero_momentum_eq.symm

@[simp]
theorem fourMomentumZeroEuclideanTubeBridge_H :
    fourMomentumZeroEuclideanTubeBridge.E.H = fourMomentumH 0 := by
  unfold fourMomentumZeroEuclideanTubeBridge
  rw [eqMp_osEuclideanTubeBridge_E_H fourMomentumS_zero_momentum_eq.symm]
  ext n α z
  change vladimirov_H (momentW z2FreeCoeff) n α z = fourMomentumH 0 n α z
  rw [vladimirov_H_eq_zero_eval (momentZeroMomentumSpectrumCondition z2FreeCoeff) n α z,
      vladimirov_H_zero_momentW, fourMomentumH_zero_momentum_eq]

noncomputable def fourMomentumZeroForwardConeEuclideanTubeBridge :
    ForwardConeOSEuclideanTubeBridge trivialRep trivialStarStructure 1 (fourMomentumS 0) :=
  fourMomentumZeroEuclideanTubeBridge.toForwardConeOSEuclideanTubeBridge

@[simp]
theorem fourMomentumZeroForwardConeEuclideanTubeBridge_W :
    fourMomentumZeroForwardConeEuclideanTubeBridge.W = fourMomentumW 0 :=
  fourMomentumZeroEuclideanTubeBridge_W

@[simp]
theorem fourMomentumZeroForwardConeEuclideanTubeBridge_H :
    fourMomentumZeroForwardConeEuclideanTubeBridge.E.H = fourMomentumH 0 :=
  fourMomentumZeroEuclideanTubeBridge_H

noncomputable def fourMomentumZeroOSReconstructedWightman :
    ScalarOSReconstructedWightman 1 (fourMomentumS 0) :=
  Eq.mp (congrArg (ScalarOSReconstructedWightman 1) fourMomentumS_zero_momentum_eq.symm)
    z2FreeOSReconstructedWightman

theorem eqMp_scalarOSReconstructedWightman_W {s t : SchwingerFamily Unit} (h : s = t)
    (P : ScalarOSReconstructedWightman 1 s) :
    (Eq.mp (congrArg (ScalarOSReconstructedWightman 1) h) P).W = P.W := by
  subst h
  rfl

theorem eqMp_scalarOSReconstructedWightman_E_H {s t : SchwingerFamily Unit} (h : s = t)
    (P : ScalarOSReconstructedWightman 1 s) :
    (Eq.mp (congrArg (ScalarOSReconstructedWightman 1) h) P).E.H = P.E.H := by
  subst h
  rfl

@[simp]
theorem fourMomentumZeroOSReconstructedWightman_W :
    fourMomentumZeroOSReconstructedWightman.W = fourMomentumW 0 := by
  unfold fourMomentumZeroOSReconstructedWightman
  rw [eqMp_scalarOSReconstructedWightman_W fourMomentumS_zero_momentum_eq.symm]
  exact fourMomentumW_zero_momentum_eq.symm

@[simp]
theorem fourMomentumZeroOSReconstructedWightman_H :
    fourMomentumZeroOSReconstructedWightman.E.H = fourMomentumH 0 := by
  unfold fourMomentumZeroOSReconstructedWightman
  rw [eqMp_scalarOSReconstructedWightman_E_H fourMomentumS_zero_momentum_eq.symm]
  ext n α z
  exact (fourMomentumH_zero_momentum_eq n α z).symm

noncomputable def fourMomentumZeroForwardConeOSReconstructedWightman :
    ForwardConeOSReconstructedWightman trivialRep trivialStarStructure 1 (fourMomentumS 0) :=
  fourMomentumZeroOSReconstructedWightman.toForwardConeOSReconstructedWightman

@[simp]
theorem fourMomentumZeroForwardConeOSReconstructedWightman_W :
    fourMomentumZeroForwardConeOSReconstructedWightman.W = fourMomentumW 0 :=
  fourMomentumZeroOSReconstructedWightman_W

@[simp]
theorem fourMomentumZeroForwardConeOSReconstructedWightman_H :
    fourMomentumZeroForwardConeOSReconstructedWightman.E.H = fourMomentumH 0 :=
  fourMomentumZeroOSReconstructedWightman_H

theorem tubeCovariant_of_tubeExtension_eq
    (R : HolomorphicLorentzRep ι) {W₁ W₂ : WightmanFamily ι}
    (E₁ : TubeExtension W₁) (E₂ : TubeExtension W₂)
    (hH : ∀ (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ),
      z ∈ forward_tube_n n → E₁.H n α z = E₂.H n α z)
    (hcov : TubeCovariant R E₂) :
    TubeCovariant R E₁ := by
  intro n A z hz hAz α
  rw [hH n α (spinorPhi (A, sl2c_conj A) • z) hAz, hcov n A z hz hAz α]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  rw [hH n β z hz]

theorem not_tubeCovariant_of_schwingerFromTube_eq_fourMomentumS
    {q : Fin 4 → ℝ} (hq : q ≠ 0) {W : WightmanFamily Unit} (E : TubeExtension W)
    (hS : ∀ (n : ℕ) (α : Fin n → Unit) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → fourMomentumS q n α x = schwingerFromTube E n α x) :
    ¬ TubeCovariant trivialRep E := by
  intro hcov
  exact not_tubeCovariant_fourMomentumTubeExtension hq
    (tubeCovariant_of_tubeExtension_eq trivialRep (fourMomentumTubeExtension q) E
      (tubeExtension_eq_of_schwingerFromTube_eq (fourMomentumTubeExtension q) E hS) hcov)

theorem isEmpty_forwardConeOSEuclideanTubeBridge_fourMomentumS
    {q : Fin 4 → ℝ} (hq : q ≠ 0) (η : ℂ) :
    IsEmpty (ForwardConeOSEuclideanTubeBridge trivialRep trivialStarStructure η
      (fourMomentumS q)) :=
  ⟨fun B => not_tubeCovariant_of_schwingerFromTube_eq_fourMomentumS hq B.E
    B.schwinger_eq B.tube_covariant⟩

theorem isEmpty_osEuclideanTubeBridge_fourMomentumS
    {q : Fin 4 → ℝ} (hq : q ≠ 0) (η : ℂ) :
    IsEmpty (OSEuclideanTubeBridge trivialRep trivialStarStructure η (fourMomentumS q)) :=
  ⟨fun B => (isEmpty_forwardConeOSEuclideanTubeBridge_fourMomentumS hq η).false
    B.toForwardConeOSEuclideanTubeBridge⟩

theorem isEmpty_forwardConeOSReconstructedWightman_fourMomentumS
    {q : Fin 4 → ℝ} (hq : q ≠ 0) (η : ℂ) :
    IsEmpty (ForwardConeOSReconstructedWightman trivialRep trivialStarStructure η
      (fourMomentumS q)) :=
  ⟨fun P => not_tubeCovariant_of_schwingerFromTube_eq_fourMomentumS hq P.E
    P.schwinger_eq P.tube_covariant⟩

theorem isEmpty_osReconstructedWightman_fourMomentumS
    {q : Fin 4 → ℝ} (hq : q ≠ 0) (η : ℂ) :
    IsEmpty (OSReconstructedWightman trivialRep trivialStarStructure η (fourMomentumS q)) :=
  ⟨fun P => (isEmpty_forwardConeOSReconstructedWightman_fourMomentumS hq η).false
    P.toForwardConeOSReconstructedWightman⟩

theorem nonempty_forwardConeOSEuclideanTubeBridge_one_fourMomentumS_iff
    (q : Fin 4 → ℝ) :
    Nonempty (ForwardConeOSEuclideanTubeBridge trivialRep trivialStarStructure 1
      (fourMomentumS q)) ↔ q = 0 := by
  refine ⟨fun ⟨B⟩ => ?_, fun h0 => ?_⟩
  · by_contra hne
    exact (isEmpty_forwardConeOSEuclideanTubeBridge_fourMomentumS hne 1).false B
  · subst h0
    exact ⟨fourMomentumZeroForwardConeEuclideanTubeBridge⟩

theorem nonempty_osEuclideanTubeBridge_one_fourMomentumS_iff (q : Fin 4 → ℝ) :
    Nonempty (OSEuclideanTubeBridge trivialRep trivialStarStructure 1
      (fourMomentumS q)) ↔ q = 0 := by
  refine ⟨fun ⟨B⟩ => ?_, fun h0 => ?_⟩
  · by_contra hne
    exact (isEmpty_osEuclideanTubeBridge_fourMomentumS hne 1).false B
  · subst h0
    exact ⟨fourMomentumZeroEuclideanTubeBridge⟩

theorem nonempty_forwardConeOSReconstructedWightman_one_fourMomentumS_iff
    (q : Fin 4 → ℝ) :
    Nonempty (ForwardConeOSReconstructedWightman trivialRep trivialStarStructure 1
      (fourMomentumS q)) ↔ q = 0 := by
  refine ⟨fun ⟨P⟩ => ?_, fun h0 => ?_⟩
  · by_contra hne
    exact (isEmpty_forwardConeOSReconstructedWightman_fourMomentumS hne 1).false P
  · subst h0
    exact ⟨fourMomentumZeroForwardConeOSReconstructedWightman⟩

theorem nonempty_scalarOSReconstructedWightman_one_fourMomentumS_iff
    (q : Fin 4 → ℝ) :
    Nonempty (ScalarOSReconstructedWightman 1 (fourMomentumS q)) ↔ q = 0 := by
  refine ⟨fun ⟨P⟩ => ?_, fun h0 => ?_⟩
  · by_contra hne
    exact (isEmpty_osReconstructedWightman_fourMomentumS hne 1).false P
  · subst h0
    exact ⟨fourMomentumZeroOSReconstructedWightman⟩

lemma contDiffBump_complex_hasCompactSupport {n : ℕ} {c : Fin n → Fin 4 → ℝ}
    (b : ContDiffBump c) :
    HasCompactSupport (fun x : Fin n → Fin 4 → ℝ => ((b x : ℝ) : ℂ)) :=
  b.hasCompactSupport.comp_left Complex.ofReal_zero

lemma contDiffBump_complex_contDiff {n : ℕ} {c : Fin n → Fin 4 → ℝ}
    (b : ContDiffBump c) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → Fin 4 → ℝ => ((b x : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp b.contDiff

noncomputable def contDiffBumpSchwartz {n : ℕ} {c : Fin n → Fin 4 → ℝ}
    (b : ContDiffBump c) : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
  (contDiffBump_complex_hasCompactSupport b).toSchwartzMap
    (contDiffBump_complex_contDiff b)

lemma contDiffBumpSchwartz_apply {n : ℕ} {c : Fin n → Fin 4 → ℝ}
    (b : ContDiffBump c) (x : Fin n → Fin 4 → ℝ) :
    contDiffBumpSchwartz b x = ((b x : ℝ) : ℂ) := rfl

lemma apply_zero_mem_closure_of_mem_forwardConeSpectralRegion_two
    {p : Fin 2 → Fin 4 → ℝ} (hp : p ∈ forwardConeSpectralRegion 2) :
    p 0 ∈ closure forward_light_cone := by
  have h0 := hp.2 0
  have hsum : (∑ i ∈ Finset.univ.filter (· ≤ (0 : Fin 2)), p i) = p 0 := by
    rw [Finset.sum_filter, Fin.sum_univ_two]
    simp
  rwa [hsum] at h0

theorem not_forwardConeSpectrumCondition_fourMomentumW
    {q : Fin 4 → ℝ} (hq : q ∉ closure forward_light_cone) :
    ¬ ForwardConeSpectrumCondition (fourMomentumW q) := by
  intro hspec
  let p₀ : Fin 2 → Fin 4 → ℝ := twoPointMomentum q
  let V : Set (Fin 2 → Fin 4 → ℝ) :=
    (fun p : Fin 2 → Fin 4 → ℝ => p 0) ⁻¹' (closure forward_light_cone)ᶜ
  have hV_open : IsOpen V := isClosed_closure.isOpen_compl.preimage (continuous_apply 0)
  have hp₀ : p₀ ∈ V := by
    change twoPointMomentum q 0 ∉ closure forward_light_cone
    rw [twoPointMomentum_zero]
    exact hq
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV_open p₀ hp₀
  let b : ContDiffBump p₀ := ⟨ε / 3, ε / 2, by positivity, by linarith⟩
  let f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ :=
    invMinkowskiFourierCLM 2 (contDiffBumpSchwartz b)
  let U : Set (Fin 2 → Fin 4 → ℝ) := {p | ε / 2 < dist p p₀}
  have hU_open : IsOpen U :=
    isOpen_lt continuous_const (continuous_id.dist continuous_const)
  have hU_sub : forwardConeSpectralRegion 2 ⊆ U := by
    intro p hp
    by_contra hnot
    have hdist : dist p p₀ ≤ ε / 2 := not_lt.mp hnot
    have hmem_ball : p ∈ Metric.ball p₀ ε :=
      Metric.mem_ball.mpr (by linarith)
    have hmem_V : p 0 ∉ closure forward_light_cone :=
      hball hmem_ball
    exact hmem_V (apply_zero_mem_closure_of_mem_forwardConeSpectralRegion_two hp)
  have hU_zero : ∀ p ∈ U, minkowskiFourier f p = 0 := by
    intro p hp
    dsimp [f]
    rw [minkowskiFourier_invMinkowskiFourierCLM_all, contDiffBumpSchwartz_apply,
        b.zero_of_le_dist (le_of_lt hp), Complex.ofReal_zero]
  have hW_zero : fourMomentumW q 2 default f = 0 :=
    hspec 2 default f ⟨U, hU_open, hU_sub, hU_zero⟩
  have hW_one : fourMomentumW q 2 default f = 1 := by
    rw [fourMomentumW_two_apply]
    dsimp [f]
    rw [minkowskiFourier_invMinkowskiFourierCLM_all, contDiffBumpSchwartz_apply]
    change ((b p₀ : ℝ) : ℂ) = 1
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le),
        Complex.ofReal_one]
  exact one_ne_zero (hW_one.symm.trans hW_zero)

theorem forwardConeSpectrumCondition_fourMomentumW_iff (q : Fin 4 → ℝ) :
    ForwardConeSpectrumCondition (fourMomentumW q) ↔ q ∈ closure forward_light_cone :=
  ⟨fun hspec => by_contra (fun hq => not_forwardConeSpectrumCondition_fourMomentumW hq hspec),
   fourMomentumW_forwardConeSpectrumCondition⟩

lemma eq_of_forall_minkowskiFourier_eq {n : ℕ} {p₁ p₂ : Fin n → Fin 4 → ℝ}
    (h : ∀ f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ,
      minkowskiFourier f p₁ = minkowskiFourier f p₂) :
    p₁ = p₂ := by
  by_contra hne
  have hd : 0 < dist p₂ p₁ := dist_pos.mpr (Ne.symm hne)
  let b : ContDiffBump p₁ := ⟨dist p₂ p₁ / 3, dist p₂ p₁ / 2, by positivity, by linarith⟩
  let ψ : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ := contDiffBumpSchwartz b
  have h_eq := h (invMinkowskiFourierCLM n ψ)
  rw [minkowskiFourier_invMinkowskiFourierCLM_all,
      minkowskiFourier_invMinkowskiFourierCLM_all] at h_eq
  change ((b p₁ : ℝ) : ℂ) = ((b p₂ : ℝ) : ℂ) at h_eq
  have hb1 : b p₁ = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
  have hb2 : b p₂ = 0 := b.zero_of_le_dist (by change dist p₂ p₁ / 2 ≤ dist p₂ p₁; linarith)
  rw [hb1, hb2] at h_eq
  norm_num at h_eq

noncomputable def boostTwoMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![2, 0; 0, 2⁻¹]

noncomputable def boostTwoSL2C : SL2C :=
  ⟨boostTwoMatrix, by
    unfold boostTwoMatrix
    rw [Matrix.det_fin_two_of]
    norm_num⟩

lemma vec_to_spinor_fixed_of_lorentzOfSL2C_mulVec_eq
    {q : Fin 4 → ℝ} (A : SL2C) (hA : (lorentzOfSL2C A).mulVec q = q) :
    A.1 * vec_to_spinor (fun μ => (q μ : ℂ)) * (sl2c_conj A).1ᵀ =
      vec_to_spinor (fun μ => (q μ : ℂ)) := by
  have hC : ((lorentzOfSL2C A).map (algebraMap ℝ ℂ)).mulVec (fun μ => (q μ : ℂ)) =
      fun μ => (q μ : ℂ) := by
    ext μ
    have hμ := congrArg (fun r : ℝ => (r : ℂ)) (congr_fun hA μ)
    dsimp [Matrix.mulVec, dotProduct] at hμ
    push_cast at hμ
    exact hμ
  rw [lorentzOfSL2C_map A] at hC
  change spinorPhi_matrix A (sl2c_conj A) *ᵥ (fun μ => (q μ : ℂ)) = _ at hC
  rw [spinorPhi_matrix_mulVec] at hC
  have h_spin := congrArg vec_to_spinor hC
  simpa [spinor_action, vec_to_spinor_right_inv] using h_spin

lemma eq_zero_of_forall_lorentzOfSL2C_mulVec_eq
    {q : Fin 4 → ℝ} (h : ∀ A : SL2C, (lorentzOfSL2C A).mulVec q = q) :
    q = 0 := by
  have hb := vec_to_spinor_fixed_of_lorentzOfSL2C_mulVec_eq boostTwoSL2C (h boostTwoSL2C)
  have hb00 := congrArg Complex.re (congr_fun (congr_fun hb 0) 0)
  have hb11 := congrArg Complex.re (congr_fun (congr_fun hb 1) 1)
  simp only [boostTwoSL2C, boostTwoMatrix, sl2c_conj, vec_to_spinor, Matrix.mul_apply,
    Fin.sum_univ_two, Fin.isValue, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.transpose_apply, Matrix.map_apply,
    add_zero, zero_mul, zero_add, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, sub_zero] at hb00 hb11
  norm_num at hb00 hb11
  have hd := vec_to_spinor_fixed_of_lorentzOfSL2C_mulVec_eq diagImagSL2C (h diagImagSL2C)
  have hd01 : (q 1 : ℂ) - (q 2 : ℂ) * Complex.I = 0 := by
    have h01 := congr_fun (congr_fun hd 0) 1
    simp only [diagImagSL2C, diagImagMatrix, sl2c_conj, vec_to_spinor_apply_01,
      Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.transpose_apply,
      Matrix.map_apply, Complex.star_def, map_zero, map_neg, Complex.conj_I,
      neg_neg, zero_mul, mul_zero, zero_add] at h01
    linear_combination (h01 - Complex.I_sq * ((q 1 : ℂ) - (q 2 : ℂ) * Complex.I)) / (-2)
  have h0 : q 0 = 0 := by linarith
  have h1 : q 1 = 0 := by simpa using congrArg Complex.re hd01
  have h2 : q 2 = 0 := by
    have him := congrArg Complex.im hd01
    simp at him
    linarith
  have h3 : q 3 = 0 := by linarith
  ext μ
  fin_cases μ <;> assumption

theorem not_poincareCovariant_fourMomentumW
    {q : Fin 4 → ℝ} (hq : q ≠ 0) :
    ¬ PoincareCovariant trivialRep (fourMomentumW q) := by
  intro hP
  apply hq
  refine eq_zero_of_forall_lorentzOfSL2C_mulVec_eq (fun A => ?_)
  have h_all : ∀ f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ,
      minkowskiFourier f ((lorentzEquiv 2 A) (twoPointMomentum q)) =
        minkowskiFourier f (twoPointMomentum q) := by
    intro f
    have hcov := wightman_lorentz_cov trivialRep (fourMomentumW q) hP 2 A⁻¹ f default
    have h_prod : (∏ i : Fin 2, trivialRep.rep A⁻¹ ((default : Fin 2 → Unit) i)
        ((default : Fin 2 → Unit) i)) = 1 :=
      Finset.prod_eq_one (fun _ _ => rfl)
    rw [Fintype.sum_unique, h_prod, one_mul] at hcov
    change fourMomentumW q 2 default (schwartzLorentzCLM 2 A⁻¹⁻¹ f) =
      fourMomentumW q 2 default f at hcov
    rw [fourMomentumW_two_apply, fourMomentumW_two_apply,
        minkowskiFourier_schwartzLorentzCLM_n 2 A⁻¹ f (twoPointMomentum q),
        inv_inv] at hcov
    exact hcov
  have h_eq := congr_fun (eq_of_forall_minkowskiFourier_eq h_all) 0
  simpa [lorentzEquiv, lorentzActLM, twoPointMomentum] using h_eq

theorem poincareCovariant_fourMomentumW_iff (q : Fin 4 → ℝ) :
    PoincareCovariant trivialRep (fourMomentumW q) ↔ q = 0 := by
  refine ⟨fun hP => ?_, fun h0 => ?_⟩
  · by_contra hne
    exact not_poincareCovariant_fourMomentumW hne hP
  · subst h0
    rw [fourMomentumW_zero_momentum_eq]
    exact momentPoincareCovariant z2FreeCoeff

lemma exists_spacelike_pos_inner {q : Fin 4 → ℝ} (hq : q ≠ 0) :
    ∃ d : Fin 4 → ℝ, is_spacelike d ∧ 0 < minkowskiInner q d := by
  by_cases hs : q 1 = 0 ∧ q 2 = 0 ∧ q 3 = 0
  · obtain ⟨h1, h2, h3⟩ := hs
    have h0 : q 0 ≠ 0 := by
      intro h0
      apply hq
      ext μ
      fin_cases μ <;> assumption
    have hp : 0 < q 0 * q 0 := mul_self_pos.mpr h0
    refine ⟨![q 0, 2 * q 0, 0, 0], ?_, ?_⟩
    · unfold is_spacelike
      rw [minkowskiInner_explicit]
      change q 0 * q 0 - (2 * q 0) * (2 * q 0) - 0 * 0 - 0 * 0 < 0
      nlinarith
    · rw [minkowskiInner_explicit]
      change 0 < q 0 * q 0 - q 1 * (2 * q 0) - q 2 * 0 - q 3 * 0
      rw [h1]
      nlinarith
  · have hpos : 0 < q 1 * q 1 + q 2 * q 2 + q 3 * q 3 := by
      by_contra hle
      push Not at hle
      apply hs
      refine ⟨mul_self_eq_zero.mp ?_, mul_self_eq_zero.mp ?_, mul_self_eq_zero.mp ?_⟩ <;>
        nlinarith [mul_self_nonneg (q 1), mul_self_nonneg (q 2), mul_self_nonneg (q 3)]
    refine ⟨![0, -q 1, -q 2, -q 3], ?_, ?_⟩
    · unfold is_spacelike
      rw [minkowskiInner_explicit]
      change (0 : ℝ) * 0 - (-q 1) * (-q 1) - (-q 2) * (-q 2) - (-q 3) * (-q 3) < 0
      nlinarith
    · rw [minkowskiInner_explicit]
      change 0 < q 0 * 0 - q 1 * (-q 1) - q 2 * (-q 2) - q 3 * (-q 3)
      nlinarith

lemma sum_alternatingMomentum_two_inner (q : Fin 4 → ℝ) (x : Fin 2 → Fin 4 → ℝ) :
    (∑ k : Fin 2, minkowskiInner (alternatingMomentum 2 q k) (x k)) =
      minkowskiInner q (x 0 - x 1) := by
  rw [Fin.sum_univ_two]
  have h0 : alternatingMomentum 2 q 0 = q := by simp [alternatingMomentum]
  have h1 : alternatingMomentum 2 q 1 = -q := by simp [alternatingMomentum]
  rw [h0, h1, minkowskiInner_explicit, minkowskiInner_explicit, minkowskiInner_explicit]
  simp only [Pi.neg_apply, Pi.sub_apply]
  ring

lemma mem_jost_points_two_of_minkowskiInner_sub_lt_zero
    {x : Fin 2 → Fin 4 → ℝ} (hsl : minkowskiInner (x 0 - x 1) (x 0 - x 1) < 0) :
    x ∈ jost_points_n 2 := by
  intro v hv
  have hsub : jost_differences_n 2 x ⊆ {x 0 - x 1} := by
    rintro v ⟨i, hi, rfl⟩
    have hi0 : i = 0 := Fin.ext (by change i.val = 0; omega)
    subst hi0
    exact rfl
  have hv' := convexHull_mono hsub hv
  rw [convexHull_singleton] at hv'
  rw [hv']
  exact hsl

theorem not_weakLocality_fourMomentumW_any {q : Fin 4 → ℝ} (hq : q ≠ 0) (η : ℂ) :
    ¬ WeakLocality η (fourMomentumW q) := by
  intro hWL
  obtain ⟨d, hd, ha⟩ := exists_spacelike_pos_inner hq
  let lam : ℝ := Real.pi / (4 * minkowskiInner q d)
  have hlam : 0 < lam := div_pos Real.pi_pos (by linarith)
  let φ : (Fin 2 → Fin 4 → ℝ) → ℝ := fun x => minkowskiInner q (x 0 - x 1)
  have hφ_cont : Continuous φ := by
    simp only [φ, minkowskiInner_explicit, Pi.sub_apply]
    fun_prop
  let sp : (Fin 2 → Fin 4 → ℝ) → ℝ := fun x => minkowskiInner (x 0 - x 1) (x 0 - x 1)
  have hsp_cont : Continuous sp := by
    simp only [sp, minkowskiInner_explicit, Pi.sub_apply]
    fun_prop
  let U : Set (Fin 2 → Fin 4 → ℝ) := {x | sp x < 0 ∧ 0 < φ x ∧ φ x < Real.pi / 2}
  have hU : IsOpen U := by
    have h1 : IsOpen {x | sp x < 0} := isOpen_lt hsp_cont continuous_const
    have h2 : IsOpen {x | 0 < φ x} := isOpen_lt continuous_const hφ_cont
    have h3 : IsOpen {x | φ x < Real.pi / 2} := isOpen_lt hφ_cont continuous_const
    exact h1.inter (h2.inter h3)
  let c : Fin 2 → Fin 4 → ℝ := fun i => if i = 0 then lam • d else 0
  have hc0 : c 0 - c 1 = lam • d := by
    ext μ
    simp [c]
  have hφc : φ c = Real.pi / 4 := by
    have h1 : φ c = lam * minkowskiInner q d := by
      simp only [φ, hc0, minkowskiInner_explicit, Pi.smul_apply, smul_eq_mul]
      ring
    rw [h1]
    simp only [lam]
    field_simp
  have hcU : c ∈ U := by
    have hsl : minkowskiInner (lam • d) (lam • d) = lam ^ 2 * minkowskiInner d d := by
      simp only [minkowskiInner_explicit, Pi.smul_apply, smul_eq_mul]
      ring
    refine ⟨?_, ?_, ?_⟩
    · simp only [sp, hc0, hsl]
      exact mul_neg_of_pos_of_neg (pow_pos hlam 2) hd
    · rw [hφc]
      positivity
    · rw [hφc]
      linarith [Real.pi_pos]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU c hcU
  let b : ContDiffBump c := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hsupp : ∀ x, b x ≠ 0 → x ∈ U := by
    intro x hx
    apply hball
    have hx' : x ∈ Function.support b := hx
    rw [b.support_eq] at hx'
    change x ∈ Metric.ball c (ε / 2) at hx'
    exact Metric.ball_subset_ball (by linarith) hx'
  let g : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ := contDiffBumpSchwartz b
  let f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ := schwartzRevCLM 2 g
  have hrev_fg : ∀ x : Fin 2 → Fin 4 → ℝ, g (fun i => x (Fin.rev i)) = f x :=
    fun x => (schwartzRevCLM_apply 2 g x).symm
  have hrev_gf : ∀ x : Fin 2 → Fin 4 → ℝ, f (fun i => x (Fin.rev i)) = g x := by
    intro x
    rw [← hrev_fg (fun i => x (Fin.rev i))]
    congr 1
    ext i μ
    rw [Fin.rev_rev]
  have hg_cb : tsupport (g : (Fin 2 → Fin 4 → ℝ) → ℂ) ⊆ Metric.closedBall c (ε / 2) := by
    refine closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall
    have hb : x ∈ Function.support b := by
      intro h0
      apply hx
      change ((b x : ℝ) : ℂ) = 0
      rw [h0]
      simp
    rw [b.support_eq] at hb
    change x ∈ Metric.ball c (ε / 2) at hb
    exact Metric.ball_subset_closedBall hb
  have hjost_g : tsupport (g : (Fin 2 → Fin 4 → ℝ) → ℂ) ⊆ jost_points_n 2 := by
    intro x hx
    have hxU : x ∈ U :=
      hball (Metric.closedBall_subset_ball (by linarith) (hg_cb hx))
    exact mem_jost_points_two_of_minkowskiInner_sub_lt_zero hxU.1
  have hf_cb : tsupport (f : (Fin 2 → Fin 4 → ℝ) → ℂ) ⊆
      (fun x : Fin 2 → Fin 4 → ℝ => fun i => x (Fin.rev i)) ⁻¹'
        Metric.closedBall c (ε / 2) := by
    refine closure_minimal (fun x hx => ?_)
      (Metric.isClosed_closedBall.preimage (continuous_pi fun i => continuous_apply (Fin.rev i)))
    have hxg : (fun i => x (Fin.rev i)) ∈ Function.support (g : (Fin 2 → Fin 4 → ℝ) → ℂ) := by
      change g (fun i => x (Fin.rev i)) ≠ 0
      rwa [hrev_fg x]
    exact hg_cb (subset_tsupport _ hxg)
  have hjost_f : tsupport (f : (Fin 2 → Fin 4 → ℝ) → ℂ) ⊆ jost_points_n 2 := by
    intro x hx
    have hyU : (fun i => x (Fin.rev i)) ∈ U :=
      hball (Metric.closedBall_subset_ball (by linarith) (hf_cb hx))
    have hsl : minkowskiInner (x 0 - x 1) (x 0 - x 1) < 0 := by
      have h : minkowskiInner (x 1 - x 0) (x 1 - x 0) < 0 := hyU.1
      simp only [minkowskiInner_explicit, Pi.sub_apply] at h ⊢
      nlinarith [h]
    exact mem_jost_points_two_of_minkowskiInner_sub_lt_zero hsl
  have hWL1 := hWL 2 default f g hjost_f hrev_fg
  have hWL2 := hWL 2 default g f hjost_g hrev_gf
  have h_def : ((default : Fin 2 → Unit) ∘ Fin.rev) = default := rfl
  rw [two_mul_two_sub_one_div_two, pow_one, h_def] at hWL1 hWL2
  have hneg := fourMomentumW_rev_eq_neg q 2 default f g hrev_fg
  rw [h_def] at hneg
  have hsum1 : ∀ x : Fin 2 → Fin 4 → ℝ,
      (∑ k : Fin 2, minkowskiInner (alternatingMomentum 2 q k) (x k)) = φ x :=
    fun x => sum_alternatingMomentum_two_inner q x
  have hsum2 : ∀ x : Fin 2 → Fin 4 → ℝ,
      (∑ k : Fin 2, minkowskiInner (alternatingMomentum 2 (-q) k) (x k)) = -φ x := by
    intro x
    rw [sum_alternatingMomentum_two_inner]
    simp only [φ, minkowskiInner_explicit, Pi.neg_apply]
    ring
  have hi1 : Integrable (fun x : Fin 2 → Fin 4 → ℝ =>
      g x * Complex.exp (-(Complex.I * ((φ x : ℝ) : ℂ)))) := by
    have h := integrable_f_mul_exp_phase 2 g (alternatingMomentum 2 q)
    simp only [hsum1] at h
    exact h
  have hi2 : Integrable (fun x : Fin 2 → Fin 4 → ℝ =>
      g x * Complex.exp (-(Complex.I * ((-φ x : ℝ) : ℂ)))) := by
    have h := integrable_f_mul_exp_phase 2 g (alternatingMomentum 2 (-q))
    simp only [hsum2] at h
    exact h
  have hWg : fourMomentumW q 2 default g =
      ∫ x : Fin 2 → Fin 4 → ℝ, g x * Complex.exp (-(Complex.I * ((φ x : ℝ) : ℂ))) := by
    rw [fourMomentumW_apply, if_pos rfl]
    unfold minkowskiFourier
    simp only [hsum1]
  have hWf : fourMomentumW q 2 default f =
      ∫ x : Fin 2 → Fin 4 → ℝ, g x * Complex.exp (-(Complex.I * ((-φ x : ℝ) : ℂ))) := by
    rw [hneg, fourMomentumW_apply, if_pos rfl]
    unfold minkowskiFourier
    simp only [hsum2]
  have hpt_sub : ∀ x : Fin 2 → Fin 4 → ℝ,
      g x * Complex.exp (-(Complex.I * ((φ x : ℝ) : ℂ))) -
        g x * Complex.exp (-(Complex.I * ((-φ x : ℝ) : ℂ))) =
      ((-2 * (b x * Real.sin (φ x)) : ℝ) : ℂ) * Complex.I := by
    intro x
    have e1 : Complex.exp (-(Complex.I * ((φ x : ℝ) : ℂ))) =
        ((Real.cos (φ x) : ℝ) : ℂ) - ((Real.sin (φ x) : ℝ) : ℂ) * Complex.I := by
      rw [show -(Complex.I * ((φ x : ℝ) : ℂ)) = ((-φ x : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_neg, Real.sin_neg]
      push_cast
      ring
    have e2 : Complex.exp (-(Complex.I * ((-φ x : ℝ) : ℂ))) =
        ((Real.cos (φ x) : ℝ) : ℂ) + ((Real.sin (φ x) : ℝ) : ℂ) * Complex.I := by
      rw [show -(Complex.I * ((-φ x : ℝ) : ℂ)) = ((φ x : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    change ((b x : ℝ) : ℂ) * _ - ((b x : ℝ) : ℂ) * _ = _
    rw [e1, e2]
    push_cast
    ring
  have hpt_add : ∀ x : Fin 2 → Fin 4 → ℝ,
      g x * Complex.exp (-(Complex.I * ((φ x : ℝ) : ℂ))) +
        g x * Complex.exp (-(Complex.I * ((-φ x : ℝ) : ℂ))) =
      ((2 * (b x * Real.cos (φ x)) : ℝ) : ℂ) := by
    intro x
    have e1 : Complex.exp (-(Complex.I * ((φ x : ℝ) : ℂ))) =
        ((Real.cos (φ x) : ℝ) : ℂ) - ((Real.sin (φ x) : ℝ) : ℂ) * Complex.I := by
      rw [show -(Complex.I * ((φ x : ℝ) : ℂ)) = ((-φ x : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_neg, Real.sin_neg]
      push_cast
      ring
    have e2 : Complex.exp (-(Complex.I * ((-φ x : ℝ) : ℂ))) =
        ((Real.cos (φ x) : ℝ) : ℂ) + ((Real.sin (φ x) : ℝ) : ℂ) * Complex.I := by
      rw [show -(Complex.I * ((-φ x : ℝ) : ℂ)) = ((φ x : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    change ((b x : ℝ) : ℂ) * _ + ((b x : ℝ) : ℂ) * _ = _
    rw [e1, e2]
    push_cast
    ring
  have h_sin_pos : 0 < ∫ x : Fin 2 → Fin 4 → ℝ, b x * Real.sin (φ x) := by
    have hcont : Continuous (fun x : Fin 2 → Fin 4 → ℝ => b x * Real.sin (φ x)) :=
      b.continuous.mul (Real.continuous_sin.comp hφ_cont)
    have hcs : HasCompactSupport (fun x : Fin 2 → Fin 4 → ℝ => b x * Real.sin (φ x)) :=
      b.hasCompactSupport.mul_right
    have hnn : 0 ≤ (fun x : Fin 2 → Fin 4 → ℝ => b x * Real.sin (φ x)) := by
      intro x
      change 0 ≤ b x * Real.sin (φ x)
      by_cases hbx : b x = 0
      · rw [hbx, zero_mul]
      · have hU' := hsupp x hbx
        exact mul_nonneg b.nonneg
          (Real.sin_pos_of_pos_of_lt_pi hU'.2.1 (by linarith [hU'.2.2, Real.pi_pos])).le
    have hc1 : b c * Real.sin (φ c) ≠ 0 := by
      have hb1 : b c = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
      rw [hb1, hφc, Real.sin_pi_div_four]
      exact mul_ne_zero one_ne_zero (div_ne_zero (Real.sqrt_ne_zero'.mpr two_pos) two_ne_zero)
    exact hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs hnn hc1
  have h_cos_pos : 0 < ∫ x : Fin 2 → Fin 4 → ℝ, b x * Real.cos (φ x) := by
    have hcont : Continuous (fun x : Fin 2 → Fin 4 → ℝ => b x * Real.cos (φ x)) :=
      b.continuous.mul (Real.continuous_cos.comp hφ_cont)
    have hcs : HasCompactSupport (fun x : Fin 2 → Fin 4 → ℝ => b x * Real.cos (φ x)) :=
      b.hasCompactSupport.mul_right
    have hnn : 0 ≤ (fun x : Fin 2 → Fin 4 → ℝ => b x * Real.cos (φ x)) := by
      intro x
      change 0 ≤ b x * Real.cos (φ x)
      by_cases hbx : b x = 0
      · rw [hbx, zero_mul]
      · have hU' := hsupp x hbx
        exact mul_nonneg b.nonneg
          (Real.cos_pos_of_mem_Ioo ⟨by linarith [hU'.2.1, Real.pi_pos], hU'.2.2⟩).le
    have hc1 : b c * Real.cos (φ c) ≠ 0 := by
      have hb1 : b c = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
      rw [hb1, hφc, Real.cos_pi_div_four]
      exact mul_ne_zero one_ne_zero (div_ne_zero (Real.sqrt_ne_zero'.mpr two_pos) two_ne_zero)
    exact hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs hnn hc1
  have h_sub_ne : fourMomentumW q 2 default g - fourMomentumW q 2 default f ≠ 0 := by
    intro h0
    rw [hWg, hWf, ← integral_sub hi1 hi2] at h0
    have h3 : (∫ x : Fin 2 → Fin 4 → ℝ,
        (((-2 * (b x * Real.sin (φ x)) : ℝ) : ℂ) * Complex.I)) = 0 :=
      (integral_congr_ae (Filter.Eventually.of_forall (fun x => (hpt_sub x).symm))).trans h0
    rw [integral_mul_const, integral_complex_ofReal] at h3
    have h4 : ∫ x : Fin 2 → Fin 4 → ℝ, -2 * (b x * Real.sin (φ x)) = 0 := by
      rcases mul_eq_zero.mp h3 with h | h
      · exact_mod_cast h
      · exact absurd h Complex.I_ne_zero
    rw [integral_const_mul] at h4
    linarith
  have h_add_ne : fourMomentumW q 2 default g + fourMomentumW q 2 default f ≠ 0 := by
    intro h0
    rw [hWg, hWf, ← integral_add hi1 hi2] at h0
    have h3 : (∫ x : Fin 2 → Fin 4 → ℝ,
        ((2 * (b x * Real.cos (φ x)) : ℝ) : ℂ)) = 0 :=
      (integral_congr_ae (Filter.Eventually.of_forall (fun x => (hpt_add x).symm))).trans h0
    rw [integral_complex_ofReal] at h3
    have h4 : ∫ x : Fin 2 → Fin 4 → ℝ, 2 * (b x * Real.cos (φ x)) = 0 := by
      exact_mod_cast h3
    rw [integral_const_mul] at h4
    linarith
  have h_sub_eq : (1 + η) * (fourMomentumW q 2 default g - fourMomentumW q 2 default f) = 0 := by
    linear_combination hWL2 - hWL1
  have h_add_eq : (1 - η) * (fourMomentumW q 2 default g + fourMomentumW q 2 default f) = 0 := by
    linear_combination hWL2 + hWL1
  have h_eta1 : 1 + η = 0 := (mul_eq_zero.mp h_sub_eq).resolve_right h_sub_ne
  have h_eta2 : 1 - η = 0 := (mul_eq_zero.mp h_add_eq).resolve_right h_add_ne
  exact one_ne_zero (by linear_combination (1 / 2 : ℂ) * h_eta1 + (1 / 2 : ℂ) * h_eta2)

theorem not_weakLocality_fourMomentumW {q : Fin 4 → ℝ} (hq : q ≠ 0) :
    ¬ WeakLocality 1 (fourMomentumW q) :=
  not_weakLocality_fourMomentumW_any hq 1

theorem weakLocality_one_fourMomentumW_iff (q : Fin 4 → ℝ) :
    WeakLocality 1 (fourMomentumW q) ↔ q = 0 := by
  refine ⟨fun hWL => ?_, fun h0 => ?_⟩
  · by_contra hne
    exact not_weakLocality_fourMomentumW hne hWL
  · subst h0
    exact fourMomentumWeakLocality_zero

theorem fourMomentum_closure_forward_light_cone_master
    {q : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone) (hne : q ≠ 0) :
    ForwardConeSpectrumCondition (fourMomentumW q) ∧
    ¬ ZeroMomentumSpectrumCondition (fourMomentumW q) ∧
    ¬ PoincareCovariant trivialRep (fourMomentumW q) ∧
    (∀ η : ℂ, ¬ WeakLocality η (fourMomentumW q)) ∧
    Positivity trivialStarStructure (fourMomentumW q) ∧
    WightmanPCT 1 trivialRep (fourMomentumW q) ∧
    TubeTranslationInvariant (fourMomentumTubeExtension q) ∧
    TubeWickHermiticity trivialStarStructure (fourMomentumTubeExtension q) ∧
    TubeWeakLocality 1 (fourMomentumTubeExtension q) ∧
    ¬ TubeCovariant trivialRep (fourMomentumTubeExtension q) ∧
    OSTranslationInvariant (fourMomentumS q) ∧
    OSHermiticity trivialStarStructure (fourMomentumS q) ∧
    OSReflectionPositive trivialStarStructure (fourMomentumS q) ∧
    OSVacuumNormalized (fourMomentumS q) ∧
    OSTimeClusterDecomposition (fourMomentumOSData q) ∧
    OSDiagonalKernelBounded trivialStarStructure (fourMomentumS q) ∧
    OSContractionCondition (fourMomentumOSData q) ∧
    (∀ η : ℂ, ¬ OSAxioms trivialRep trivialStarStructure η (fourMomentumS q)) ∧
    (∀ η : ℂ,
      IsEmpty (ForwardConeOSReconstructedWightman trivialRep trivialStarStructure η
        (fourMomentumS q))) :=
  ⟨fourMomentumW_forwardConeSpectrumCondition hq,
   not_zeroMomentumSpectrumCondition_fourMomentumW hne,
   not_poincareCovariant_fourMomentumW hne,
   not_weakLocality_fourMomentumW_any hne,
   fourMomentumW_positivity q,
   fourMomentumW_pct q,
   fourMomentumTubeTranslationInvariant q,
   fourMomentumTubeWickHermiticity q,
   fourMomentumTubeWeakLocality_one q,
   not_tubeCovariant_fourMomentumTubeExtension hne,
   fourMomentumOSTranslationInvariant q,
   fourMomentumOSHermiticity q,
   fourMomentumOSReflectionPositive q,
   fourMomentumS_vacuumNormalized q,
   fourMomentumOSTimeCluster_of_mem_closure_forward_light_cone hq hne,
   fourMomentumOSDiagonalKernelBounded_of_mem_closure_forward_light_cone hq,
   fourMomentumOSContraction_of_mem_closure_forward_light_cone hq,
   not_osAxioms_fourMomentumS hne,
   isEmpty_forwardConeOSReconstructedWightman_fourMomentumS hne⟩

theorem fourMomentum_closure_forward_light_cone_hilbert
    {q : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone) :
    Nonempty (OSHilbert (fourMomentumOSData q) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2)) ∧
    Nonempty (OSSpectralDecomposition (fourMomentumOSData q)
      (fourMomentumOSContraction_of_mem_closure_forward_light_cone hq) 2) ∧
    Nonempty (OSHolomorphicSemigroup (fourMomentumOSData q)
      (fourMomentumOSContraction_of_mem_closure_forward_light_cone hq)) ∧
    Nonempty (OSSpectralMeasure (fourMomentumOSData q)
      (fourMomentumOSContraction_of_mem_closure_forward_light_cone hq) (Fin 2)) :=
  ⟨⟨fourMomentumHilbertLinearIsometryEquiv q⟩,
   ⟨fourMomentumOSSpectralDecomposition_of_mem_closure_forward_light_cone hq⟩,
   ⟨fourMomentumOSHolomorphicSemigroup_of_mem_closure_forward_light_cone hq⟩,
   ⟨fourMomentumOSSpectralMeasure_of_mem_closure_forward_light_cone hq⟩⟩

theorem fourMomentum_axiom_characterization_master (q : Fin 4 → ℝ) :
    (ForwardConeSpectrumCondition (fourMomentumW q) ↔ q ∈ closure forward_light_cone) ∧
    (ZeroMomentumSpectrumCondition (fourMomentumW q) ↔ q = 0) ∧
    (PoincareCovariant trivialRep (fourMomentumW q) ↔ q = 0) ∧
    (WeakLocality 1 (fourMomentumW q) ↔ q = 0) ∧
    (TubeCovariant trivialRep (fourMomentumTubeExtension q) ↔ q = 0) ∧
    (OSScalarRotInvariant (fourMomentumS q) ↔ q = euclidTimeVec (q 0)) ∧
    (OSSpinorRotCovariant trivialRep (fourMomentumS q) ↔ q = euclidTimeVec (q 0)) ∧
    (EuclidRotCovariant trivialRep (fourMomentumS q) ↔ q = 0) ∧
    (OSDiagonalKernelBounded trivialStarStructure (fourMomentumS q) ↔ 0 ≤ q 0) ∧
    (OSContractionCondition (fourMomentumOSData q) ↔ 0 ≤ q 0) ∧
    (OSTimeClusterDecomposition (fourMomentumOSData q) ↔ 0 < q 0) ∧
    (OSAxioms trivialRep trivialStarStructure 1 (fourMomentumS q) ↔ q = 0) ∧
    (Nonempty (ForwardConeOSEuclideanTubeBridge trivialRep trivialStarStructure 1
      (fourMomentumS q)) ↔ q = 0) ∧
    (Nonempty (OSEuclideanTubeBridge trivialRep trivialStarStructure 1
      (fourMomentumS q)) ↔ q = 0) ∧
    (Nonempty (ForwardConeOSReconstructedWightman trivialRep trivialStarStructure 1
      (fourMomentumS q)) ↔ q = 0) ∧
    (Nonempty (ScalarOSReconstructedWightman 1 (fourMomentumS q)) ↔ q = 0) :=
  ⟨forwardConeSpectrumCondition_fourMomentumW_iff q,
   zeroMomentumSpectrumCondition_fourMomentumW_iff q,
   poincareCovariant_fourMomentumW_iff q,
   weakLocality_one_fourMomentumW_iff q,
   tubeCovariant_fourMomentumTubeExtension_iff q,
   osScalarRotInvariant_fourMomentumS_iff q,
   osSpinorRotCovariant_fourMomentumS_iff q,
   euclidRotCovariant_fourMomentumS_iff q,
   osDiagonalKernelBounded_fourMomentumS_iff q,
   osContractionCondition_fourMomentumOSData_iff q,
   osTimeClusterDecomposition_fourMomentumOSData_iff q,
   osAxioms_one_fourMomentumS_iff q,
   nonempty_forwardConeOSEuclideanTubeBridge_one_fourMomentumS_iff q,
   nonempty_osEuclideanTubeBridge_one_fourMomentumS_iff q,
   nonempty_forwardConeOSReconstructedWightman_one_fourMomentumS_iff q,
   nonempty_scalarOSReconstructedWightman_one_fourMomentumS_iff q⟩

theorem analyticAt_fourMomentumH (q : Fin 4 → ℝ) (n : ℕ) (α : Fin n → Unit)
    (z : Fin n → Fin 4 → ℂ) :
    AnalyticAt ℂ (fourMomentumH q n α) z := by
  unfold fourMomentumH
  by_cases hn : n % 2 = 0
  · simp only [if_pos hn]
    exact vladimirov_kernel_analyticAt n (alternatingMomentum n q) z
  · simp only [if_neg hn]
    exact analyticAt_const

theorem integrable_fourMomentumH_line_mul_f (q : Fin 4 → ℝ)
    (n : ℕ) (α : Fin n → Unit) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (v : Fin 4 → ℝ) (t : ℝ) :
    Integrable (fun x : Fin n → Fin 4 → ℝ =>
      fourMomentumH q n α (tubeBoundaryLine n x v t) * f x) volume := by
  unfold fourMomentumH
  by_cases hn : n % 2 = 0
  · simp only [if_pos hn]
    exact integrable_vladimirov_kernel_line_mul_f n f (alternatingMomentum n q) v t
  · simp only [if_neg hn, zero_mul]
    exact integrable_zero _ _ _

noncomputable def multiMomentumSpectralFamily (m : ℕ) (w : Fin m → ℝ)
    (q : Fin m → Fin 4 → ℝ) (hq : ∀ r : Fin m, q r ∈ closure forward_light_cone) :
    ForwardConeSpectralFamily Unit where
  m _ := m
  c n _ k := if n % 2 = 0 then (w k : ℂ) else 0
  p n _ k := if n % 2 = 0 then alternatingMomentum n (q k) else 0
  mem_forwardCone n _ k := by
    by_cases hn : n % 2 = 0
    · rw [if_pos hn]
      exact alternatingMomentum_mem_forwardConeSpectralRegion n hn (hq k)
    · rw [if_neg hn]
      exact zero_mem_forwardConeSpectralRegion n

noncomputable def multiMomentumW (m : ℕ) (w : Fin m → ℝ) (q : Fin m → Fin 4 → ℝ) :
    WightmanFamily Unit :=
  fun n α => ∑ r : Fin m, (w r : ℂ) • fourMomentumW (q r) n α

@[simp]
theorem multiMomentumW_apply (m : ℕ) (w : Fin m → ℝ) (q : Fin m → Fin 4 → ℝ)
    (n : ℕ) (α : Fin n → Unit) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    multiMomentumW m w q n α f =
      ∑ r : Fin m, (w r : ℂ) * fourMomentumW (q r) n α f := by
  dsimp [multiMomentumW]
  rw [_root_.sum_apply]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [_root_.smul_apply]
  rfl

noncomputable def multiMomentumH (m : ℕ) (w : Fin m → ℝ) (q : Fin m → Fin 4 → ℝ)
    (n : ℕ) (α : Fin n → Unit) (z : Fin n → Fin 4 → ℂ) : ℂ :=
  ∑ r : Fin m, (w r : ℂ) * fourMomentumH (q r) n α z

@[simp]
theorem multiMomentumSpectralFamily_toWightmanFamily
    {m : ℕ} (w : Fin m → ℝ) {q : Fin m → Fin 4 → ℝ}
    (hq : ∀ r : Fin m, q r ∈ closure forward_light_cone) :
    (multiMomentumSpectralFamily m w q hq).toWightmanFamily =
      multiMomentumW m w q := by
  ext n α f
  rw [ForwardConeSpectralFamily.toWightmanFamily_apply, multiMomentumW_apply]
  unfold multiMomentumSpectralFamily
  dsimp only
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [fourMomentumW_apply]
  split_ifs <;> simp

@[simp]
theorem multiMomentumSpectralFamily_H
    {m : ℕ} (w : Fin m → ℝ) {q : Fin m → Fin 4 → ℝ}
    (hq : ∀ r : Fin m, q r ∈ closure forward_light_cone)
    (n : ℕ) (α : Fin n → Unit) (z : Fin n → Fin 4 → ℂ) :
    (multiMomentumSpectralFamily m w q hq).H n α z =
      multiMomentumH m w q n α z := by
  unfold ForwardConeSpectralFamily.H multiMomentumSpectralFamily multiMomentumH
  dsimp only
  refine Finset.sum_congr rfl (fun r _ => ?_)
  unfold fourMomentumH
  split_ifs <;> simp

theorem analyticAt_multiMomentumH (m : ℕ) (w : Fin m → ℝ) (q : Fin m → Fin 4 → ℝ)
    (n : ℕ) (α : Fin n → Unit) (z : Fin n → Fin 4 → ℂ) :
    AnalyticAt ℂ (multiMomentumH m w q n α) z := by
  unfold multiMomentumH
  refine analyticAt_finset_sum_normed Finset.univ (fun r _ => ?_)
  exact analyticAt_const.mul (analyticAt_fourMomentumH (q r) n α z)

theorem analyticOnNhd_multiMomentumH (m : ℕ) (w : Fin m → ℝ) (q : Fin m → Fin 4 → ℝ)
    (n : ℕ) (α : Fin n → Unit) (s : Set (Fin n → Fin 4 → ℂ)) :
    AnalyticOnNhd ℂ (multiMomentumH m w q n α) s :=
  fun z _ => analyticAt_multiMomentumH m w q n α z

theorem analyticOn_multiMomentumH (m : ℕ) (w : Fin m → ℝ) (q : Fin m → Fin 4 → ℝ)
    (n : ℕ) (α : Fin n → Unit) (s : Set (Fin n → Fin 4 → ℂ)) :
    AnalyticOn ℂ (multiMomentumH m w q n α) s :=
  (analyticOnNhd_multiMomentumH m w q n α s).analyticOn

theorem tendsto_integral_multiMomentumH_line_mul_f (m : ℕ) (w : Fin m → ℝ)
    (q : Fin m → Fin 4 → ℝ) (n : ℕ) (α : Fin n → Unit)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (v : Fin 4 → ℝ)
    (hv : v ∈ forward_light_cone) :
    Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        multiMomentumH m w q n α (tubeBoundaryLine n x v t) * f x)
      (𝓝[>] 0)
      (𝓝 (multiMomentumW m w q n α f)) := by
  have h_eq : (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        multiMomentumH m w q n α (tubeBoundaryLine n x v t) * f x) =
      (fun t : ℝ => ∑ r : Fin m, (w r : ℂ) *
        (∫ x : Fin n → Fin 4 → ℝ,
          fourMomentumH (q r) n α (tubeBoundaryLine n x v t) * f x)) := by
    ext t
    have h_int : (fun x : Fin n → Fin 4 → ℝ =>
          multiMomentumH m w q n α (tubeBoundaryLine n x v t) * f x) =
        (fun x : Fin n → Fin 4 → ℝ =>
          ∑ r : Fin m, (w r : ℂ) *
            (fourMomentumH (q r) n α (tubeBoundaryLine n x v t) * f x)) := by
      ext x
      dsimp [multiMomentumH]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun r _ => mul_assoc _ _ _)
    rw [h_int, integral_finsetSum]
    · refine Finset.sum_congr rfl (fun r _ => integral_const_mul _ _)
    · intro r _
      exact (integrable_fourMomentumH_line_mul_f (q r) n α f v t).const_mul (w r : ℂ)
  rw [h_eq, multiMomentumW_apply]
  refine tendsto_finsetSum Finset.univ (fun r _ => ?_)
  exact ((fourMomentumTubeExtension (q r)).boundary n α f v hv).const_mul (w r : ℂ)

noncomputable def multiMomentumTubeExtension (m : ℕ) (w : Fin m → ℝ)
    (q : Fin m → Fin 4 → ℝ) :
    TubeExtension (multiMomentumW m w q) where
  H := multiMomentumH m w q
  analytic n α := analyticOn_multiMomentumH m w q n α (forward_tube_n n)
  boundary n α f v hv := tendsto_integral_multiMomentumH_line_mul_f m w q n α f v hv

@[simp]
theorem multiMomentumTubeExtension_H (m : ℕ) (w : Fin m → ℝ) (q : Fin m → Fin 4 → ℝ) :
    (multiMomentumTubeExtension m w q).H = multiMomentumH m w q := rfl

noncomputable def multiMomentumS (m : ℕ) (w : Fin m → ℝ) (q : Fin m → Fin 4 → ℝ) :
    SchwingerFamily Unit :=
  schwingerFromTube (multiMomentumTubeExtension m w q)

@[simp]
theorem multiMomentumS_apply (m : ℕ) (w : Fin m → ℝ) (q : Fin m → Fin 4 → ℝ)
    (n : ℕ) (α : Fin n → Unit) (x : Fin n → Fin 4 → ℝ) :
    multiMomentumS m w q n α x =
      ∑ r : Fin m, (w r : ℂ) * fourMomentumS (q r) n α x := rfl

@[simp]
theorem multiMomentumH_zero (m : ℕ) (w : Fin m → ℝ) (q : Fin m → Fin 4 → ℝ)
    (α : Fin 0 → Unit) (z : Fin 0 → Fin 4 → ℂ) :
    multiMomentumH m w q 0 α z = ((∑ r : Fin m, w r : ℝ) : ℂ) := by
  unfold multiMomentumH
  simp

@[simp]
theorem multiMomentumS_zero (m : ℕ) (w : Fin m → ℝ) (q : Fin m → Fin 4 → ℝ)
    (α : Fin 0 → Unit) (x : Fin 0 → Fin 4 → ℝ) :
    multiMomentumS m w q 0 α x = ((∑ r : Fin m, w r : ℝ) : ℂ) := by
  rw [multiMomentumS_apply]
  simp

theorem multiMomentumS_vacuumNormalized_iff (m : ℕ) (w : Fin m → ℝ)
    (q : Fin m → Fin 4 → ℝ) :
    OSVacuumNormalized (multiMomentumS m w q) ↔ ∑ r : Fin m, w r = 1 := by
  unfold OSVacuumNormalized
  rw [multiMomentumS_zero]
  exact_mod_cast Iff.rfl

theorem multiMomentumS_vacuumNormalized {m : ℕ} {w : Fin m → ℝ}
    (hw : ∑ r : Fin m, w r = 1) (q : Fin m → Fin 4 → ℝ) :
    OSVacuumNormalized (multiMomentumS m w q) :=
  (multiMomentumS_vacuumNormalized_iff m w q).mpr hw

@[simp]
theorem multiMomentumW_one_const_one (q₀ : Fin 4 → ℝ) :
    multiMomentumW 1 (fun _ => 1) (fun _ => q₀) = fourMomentumW q₀ := by
  ext n α f
  rw [multiMomentumW_apply, Fin.sum_univ_one]
  simp

@[simp]
theorem multiMomentumH_one_const_one (q₀ : Fin 4 → ℝ) :
    multiMomentumH 1 (fun _ => 1) (fun _ => q₀) = fourMomentumH q₀ := by
  ext n α z
  unfold multiMomentumH
  rw [Fin.sum_univ_one]
  simp

@[simp]
theorem multiMomentumS_one_const_one (q₀ : Fin 4 → ℝ) :
    multiMomentumS 1 (fun _ => 1) (fun _ => q₀) = fourMomentumS q₀ := by
  ext n α x
  rw [multiMomentumS_apply, Fin.sum_univ_one]
  simp

@[simp]
theorem multiMomentumH_two_euclidTimeVec (m : ℕ) (w E : Fin m → ℝ)
    (α : Fin 2 → Unit) (z : Fin 2 → Fin 4 → ℂ) :
    multiMomentumH m w (fun r => euclidTimeVec (E r)) 2 α z =
      discreteKallenLehmannTube m w E z := by
  unfold multiMomentumH discreteKallenLehmannTube
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [fourMomentumH_two_euclidTimeVec]

@[simp]
theorem multiMomentumS_two_euclidTimeVec (m : ℕ) (w E : Fin m → ℝ)
    (α : Fin 2 → Unit) (x : Fin 2 → Fin 4 → ℝ) :
    multiMomentumS m w (fun r => euclidTimeVec (E r)) 2 α x =
      discreteKallenLehmannEuclid m w E x := by
  rw [multiMomentumS_apply]
  unfold discreteKallenLehmannEuclid
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [fourMomentumS_two_euclidTimeVec]

theorem multiMomentumH_two_euclidTimeVec_eq_measureKallenLehmannTube
    (m : ℕ) (w E : Fin m → ℝ) (α : Fin 2 → Unit) (z : Fin 2 → Fin 4 → ℂ) :
    multiMomentumH m w (fun r => euclidTimeVec (E r)) 2 α z =
      measureKallenLehmannTube Measure.count w E z := by
  rw [multiMomentumH_two_euclidTimeVec,
      measureKallenLehmannTube_count_eq_discreteKallenLehmannTube]

theorem multiMomentumS_two_euclidTimeVec_eq_measureKallenLehmannEuclid
    (m : ℕ) (w E : Fin m → ℝ) (α : Fin 2 → Unit) (x : Fin 2 → Fin 4 → ℝ) :
    multiMomentumS m w (fun r => euclidTimeVec (E r)) 2 α x =
      measureKallenLehmannEuclid Measure.count w E x := by
  rw [multiMomentumS_two_euclidTimeVec,
      measureKallenLehmannEuclid_count_eq_discreteKallenLehmannEuclid]

theorem multiMomentumTubeTranslationInvariant (m : ℕ) (w : Fin m → ℝ)
    (q : Fin m → Fin 4 → ℝ) :
    TubeTranslationInvariant (multiMomentumTubeExtension m w q) := by
  intro n α z a hz
  change multiMomentumH m w q n α (fun i => z i + a) = multiMomentumH m w q n α z
  unfold multiMomentumH
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have hr : fourMomentumH (q r) n α (fun i => z i + a) = fourMomentumH (q r) n α z :=
    fourMomentumTubeTranslationInvariant (q r) n α z a hz
  rw [hr]

theorem multiMomentumOSTranslationInvariant (m : ℕ) (w : Fin m → ℝ)
    (q : Fin m → Fin 4 → ℝ) :
    OSTranslationInvariant (multiMomentumS m w q) :=
  schwingerFromTube_translation_invariant (multiMomentumTubeExtension m w q)
    (multiMomentumTubeTranslationInvariant m w q)

theorem multiMomentumW_translationInvariant (m : ℕ) (w : Fin m → ℝ)
    (q : Fin m → Fin 4 → ℝ) (n : ℕ) (α : Fin n → Unit) (a : Fin 4 → ℝ)
    (f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hf' : ∀ x : Fin n → Fin 4 → ℝ, f' (fun i => x i + a) = f x) :
    multiMomentumW m w q n α f' = multiMomentumW m w q n α f :=
  wightman_translationInvariant_of_tubeTranslationInvariant
    (multiMomentumTubeExtension m w q)
    (multiMomentumTubeTranslationInvariant m w q) n α a f f' hf'

theorem multiMomentumTubeWickHermiticity (m : ℕ) (w : Fin m → ℝ)
    (q : Fin m → Fin 4 → ℝ) :
    TubeWickHermiticity trivialStarStructure (multiMomentumTubeExtension m w q) := by
  intro n α z hz hstar
  simp only [Fintype.sum_unique, trivialStarStructure, Matrix.one_apply_eq,
    Finset.prod_const_one, one_mul, multiMomentumTubeExtension_H, multiMomentumH,
    star_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have hr := fourMomentumTubeWickHermiticity (q r) n α z hz hstar
  simp only [Fintype.sum_unique, trivialStarStructure, Matrix.one_apply_eq,
    Finset.prod_const_one, one_mul, fourMomentumTubeExtension_H] at hr
  rw [star_mul', Complex.star_def, Complex.conj_ofReal, ← Complex.star_def, hr]

theorem multiMomentumOSHermiticity (m : ℕ) (w : Fin m → ℝ)
    (q : Fin m → Fin 4 → ℝ) :
    OSHermiticity trivialStarStructure (multiMomentumS m w q) :=
  schwingerFromTube_os_hermiticity trivialStarStructure
    (multiMomentumTubeExtension m w q)
    (multiMomentumTubeWickHermiticity m w q)

theorem multiMomentumTubeWeakLocality_one (m : ℕ) (w : Fin m → ℝ)
    (q : Fin m → Fin 4 → ℝ) :
    TubeWeakLocality 1 (multiMomentumTubeExtension m w q) := by
  intro n α z hz
  rw [one_pow, one_mul]
  change multiMomentumH m w q n α (-(z ∘ Fin.rev)) =
    multiMomentumH m w q n (α ∘ Fin.rev) z
  unfold multiMomentumH
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have hr := fourMomentumTubeWeakLocality_one (q r) n α z hz
  rw [one_pow, one_mul] at hr
  exact congrArg ((w r : ℂ) * ·) hr

theorem multiMomentumOSSymmetric (m : ℕ) (w : Fin m → ℝ) (q : Fin m → Fin 4 → ℝ)
    (n : ℕ) (α : Fin n → Unit) (x : Fin n → Fin 4 → ℝ)
    (hx : x ∈ orderedEuclidN n) :
    multiMomentumS m w q n α (-(x ∘ Fin.rev)) =
      (1 : ℂ) ^ (n * (n - 1) / 2) * multiMomentumS m w q n (α ∘ Fin.rev) x :=
  schwingerFromTube_weakLocality (multiMomentumTubeExtension m w q)
    (multiMomentumTubeWeakLocality_one m w q) n α x hx

theorem multiMomentumW_pct (m : ℕ) (w : Fin m → ℝ) (q : Fin m → Fin 4 → ℝ) :
    WightmanPCT 1 trivialRep (multiMomentumW m w q) :=
  wightman_pct_trivialRep_of_tube (multiMomentumTubeExtension m w q)
    (multiMomentumTubeTranslationInvariant m w q)
    (multiMomentumTubeWeakLocality_one m w q)

theorem multiMomentumS_contDiffOn (m : ℕ) (w : Fin m → ℝ) (q : Fin m → Fin 4 → ℝ)
    (n : ℕ) (α : Fin n → Unit) :
    ContDiffOn ℝ (⊤ : ℕ∞) (multiMomentumS m w q n α) (orderedEuclidN n) :=
  schwingerFromTube_contDiffOn (multiMomentumTubeExtension m w q) n α

theorem osScalarRotInvariant_multiMomentumS_of_forall_eq_euclidTimeVec
    (m : ℕ) (w : Fin m → ℝ) {q : Fin m → Fin 4 → ℝ}
    (hq : ∀ r : Fin m, q r = euclidTimeVec (q r 0)) :
    OSScalarRotInvariant (multiMomentumS m w q) := by
  intro n U α x hx
  rw [multiMomentumS_apply, multiMomentumS_apply]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have hr : OSScalarRotInvariant (fourMomentumS (q r)) := by
    rw [hq r]
    exact fourMomentumS_euclidTimeVec_scalarRotInvariant (q r 0)
  rw [hr n U α x hx]

theorem osSpinorRotCovariant_multiMomentumS_of_forall_eq_euclidTimeVec
    (m : ℕ) (w : Fin m → ℝ) {q : Fin m → Fin 4 → ℝ}
    (hq : ∀ r : Fin m, q r = euclidTimeVec (q r 0)) :
    OSSpinorRotCovariant trivialRep (multiMomentumS m w q) := by
  intro n U α x hx
  have h_prod :
      (∏ i : Fin n, osSpinorRotMatrix trivialRep U (α i) (α i)) = 1 :=
    Finset.prod_eq_one (fun i _ => rfl)
  rw [Fintype.sum_unique, h_prod, one_mul]
  exact osScalarRotInvariant_multiMomentumS_of_forall_eq_euclidTimeVec m w hq n U α x hx

theorem osScalarRotInvariant_multiMomentumS_euclidTimeVec
    (m : ℕ) (w E : Fin m → ℝ) :
    OSScalarRotInvariant (multiMomentumS m w (fun r => euclidTimeVec (E r))) :=
  osScalarRotInvariant_multiMomentumS_of_forall_eq_euclidTimeVec m w
    (fun r => by simp [euclidTimeVec])

theorem osSpinorRotCovariant_multiMomentumS_euclidTimeVec
    (m : ℕ) (w E : Fin m → ℝ) :
    OSSpinorRotCovariant trivialRep
      (multiMomentumS m w (fun r => euclidTimeVec (E r))) :=
  osSpinorRotCovariant_multiMomentumS_of_forall_eq_euclidTimeVec m w
    (fun r => by simp [euclidTimeVec])

lemma sum_sum_sum_fin_comm {α β : Type*} (s : Finset α) (t : Finset β)
    (m : ℕ) (f : α → β → Fin m → ℂ) :
    (∑ a ∈ s, ∑ b ∈ t, ∑ r : Fin m, f a b r) =
      ∑ r : Fin m, ∑ a ∈ s, ∑ b ∈ t, f a b r := by
  have h1 : ∀ a ∈ s,
      (∑ b ∈ t, ∑ r : Fin m, f a b r) = ∑ r : Fin m, ∑ b ∈ t, f a b r :=
    fun _ _ => Finset.sum_comm
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]

theorem multiMomentumW_sesquilinear_eq (m : ℕ) (w : Fin m → ℝ) (q : Fin m → Fin 4 → ℝ)
    (N : ℕ) (G : ∀ j k : ℕ, (Fin j → Unit) → (Fin k → Unit) →
      SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ) :
    (∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ∑ α : Fin j → Unit, ∑ α' : Fin k → Unit, ∑ β : Fin j → Unit,
        (∏ i : Fin j, trivialStarStructure.C (α i) (β i)) *
          multiMomentumW m w q (j + k) (Fin.append (β ∘ Fin.rev) α') (G j k α α')) =
      ∑ r : Fin m, (w r : ℂ) *
        (∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
          ∑ α : Fin j → Unit, ∑ α' : Fin k → Unit, ∑ β : Fin j → Unit,
            (∏ i : Fin j, trivialStarStructure.C (α i) (β i)) *
              fourMomentumW (q r) (j + k) (Fin.append (β ∘ Fin.rev) α') (G j k α α')) := by
  have h_inner : ∀ j k : ℕ,
      (∑ α : Fin j → Unit, ∑ α' : Fin k → Unit, ∑ β : Fin j → Unit,
        (∏ i : Fin j, trivialStarStructure.C (α i) (β i)) *
          multiMomentumW m w q (j + k) (Fin.append (β ∘ Fin.rev) α') (G j k α α')) =
      ∑ r : Fin m, (w r : ℂ) *
        (∑ α : Fin j → Unit, ∑ α' : Fin k → Unit, ∑ β : Fin j → Unit,
          (∏ i : Fin j, trivialStarStructure.C (α i) (β i)) *
            fourMomentumW (q r) (j + k) (Fin.append (β ∘ Fin.rev) α') (G j k α α')) := by
    intro j k
    simp only [Fintype.sum_unique, trivialStarStructure, Matrix.one_apply_eq,
      Finset.prod_const_one, one_mul, multiMomentumW_apply]
  simp_rw [h_inner]
  rw [sum_sum_sum_fin_comm]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  simp_rw [Finset.mul_sum]

theorem multiMomentumW_positivity {m : ℕ} {w : Fin m → ℝ}
    (hw : ∀ r : Fin m, 0 ≤ w r) (q : Fin m → Fin 4 → ℝ) :
    Positivity trivialStarStructure (multiMomentumW m w q) := by
  intro N F G hG
  rw [multiMomentumW_sesquilinear_eq]
  refine Finset.sum_nonneg (fun r _ => ?_)
  have h_wr : (0 : ℂ) ≤ (w r : ℂ) := by exact_mod_cast hw r
  exact mul_nonneg h_wr (fourMomentumW_positivity (q r) N F G hG)

theorem osKernel_multiMomentumS_eq (m : ℕ) (w : Fin m → ℝ) (q : Fin m → Fin 4 → ℝ)
    (A B : OSConfig Unit) :
    osKernel trivialStarStructure (multiMomentumS m w q) A B =
      ∑ r : Fin m, (w r : ℂ) * osKernel trivialStarStructure (fourMomentumS (q r)) A B := by
  rcases A with ⟨j, α, x, hx⟩
  rcases B with ⟨k, α', y, hy⟩
  unfold osKernel
  simp only [Fintype.sum_unique, trivialStarStructure, Matrix.one_apply_eq,
    Finset.prod_const_one, one_mul, multiMomentumS_apply]

theorem osPreInner_multiMomentumS_eq (m : ℕ) (w : Fin m → ℝ) (q : Fin m → Fin 4 → ℝ)
    (Ψ Φ : OSConfig Unit →₀ ℂ) :
    osPreInner trivialStarStructure (multiMomentumS m w q) Ψ Φ =
      ∑ r : Fin m, (w r : ℂ) * osPreInner trivialStarStructure (fourMomentumS (q r)) Ψ Φ := by
  unfold osPreInner Finsupp.sum
  simp_rw [osKernel_multiMomentumS_eq, Finset.mul_sum]
  rw [sum_sum_sum_fin_comm]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  refine Finset.sum_congr rfl (fun A _ => Finset.sum_congr rfl (fun B _ => ?_))
  ring

theorem multiMomentumOSReflectionPositive {m : ℕ} {w : Fin m → ℝ}
    (hw : ∀ r : Fin m, 0 ≤ w r) (q : Fin m → Fin 4 → ℝ) :
    OSReflectionPositive trivialStarStructure (multiMomentumS m w q) := by
  intro Ψ
  rw [osPreInner_multiMomentumS_eq, Complex.re_sum]
  refine Finset.sum_nonneg (fun r _ => ?_)
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (hw r) (fourMomentumOSReflectionPositive (q r) Ψ)

noncomputable def multiMomentumOSData {m : ℕ} {w : Fin m → ℝ}
    (hw : ∀ r : Fin m, 0 ≤ w r) (q : Fin m → Fin 4 → ℝ) :
    OSReflectionPositiveData trivialRep trivialStarStructure where
  𝒮 := multiMomentumS m w q
  hermiticity := multiMomentumOSHermiticity m w q
  positivity := multiMomentumOSReflectionPositive hw q

@[simp]
lemma multiMomentumOSData_S {m : ℕ} {w : Fin m → ℝ}
    (hw : ∀ r : Fin m, 0 ≤ w r) (q : Fin m → Fin 4 → ℝ) :
    (multiMomentumOSData hw q).𝒮 = multiMomentumS m w q := rfl

theorem multiMomentumW_forwardConeSpectrumCondition {m : ℕ} (w : Fin m → ℝ)
    {q : Fin m → Fin 4 → ℝ} (hq : ∀ r : Fin m, q r ∈ closure forward_light_cone) :
    ForwardConeSpectrumCondition (multiMomentumW m w q) := by
  rw [← multiMomentumSpectralFamily_toWightmanFamily w hq]
  exact (multiMomentumSpectralFamily m w q hq).forwardConeSpectrumCondition

theorem norm_multiMomentumH_le_sum {m : ℕ} {w : Fin m → ℝ}
    (hw : ∀ r : Fin m, 0 ≤ w r) {q : Fin m → Fin 4 → ℝ}
    (hq : ∀ r : Fin m, q r ∈ closure forward_light_cone)
    (n : ℕ) (α : Fin n → Unit) {z : Fin n → Fin 4 → ℂ} (hz : z ∈ forward_tube_n n) :
    ‖multiMomentumH m w q n α z‖ ≤ ∑ r : Fin m, w r := by
  unfold multiMomentumH
  refine (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum (fun r _ => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw r)]
  have h_le := norm_fourMomentumH_le_one (hq r) n α hz
  nlinarith [hw r]

theorem multiMomentumOSDiagonalKernelBounded {m : ℕ} (w : Fin m → ℝ)
    {q : Fin m → Fin 4 → ℝ} (hq0 : ∀ r : Fin m, 0 ≤ q r 0) :
    OSDiagonalKernelBounded trivialStarStructure (multiMomentumS m w q) := by
  intro A
  choose c hc using fun r : Fin m => fourMomentumOSDiagonalKernelBounded (hq0 r) A
  refine ⟨∑ r : Fin m, ‖w r‖ * c r, fun τ hτ => ?_⟩
  rw [osKernel_multiMomentumS_eq]
  refine (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum (fun r _ => ?_))
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_left (hc r τ hτ) (norm_nonneg (w r))

theorem multiMomentumOSContraction {m : ℕ} {w : Fin m → ℝ}
    (hw : ∀ r : Fin m, 0 ≤ w r) {q : Fin m → Fin 4 → ℝ}
    (hq0 : ∀ r : Fin m, 0 ≤ q r 0) :
    OSContractionCondition (multiMomentumOSData hw q) :=
  osContractionCondition_of_diagonalKernelBounded (multiMomentumOSData hw q)
    (multiMomentumOSTranslationInvariant m w q)
    (multiMomentumOSDiagonalKernelBounded w hq0)

theorem multiMomentumOSDiagonalKernelBounded_of_mem_closure_forward_light_cone
    {m : ℕ} (w : Fin m → ℝ) {q : Fin m → Fin 4 → ℝ}
    (hq : ∀ r : Fin m, q r ∈ closure forward_light_cone) :
    OSDiagonalKernelBounded trivialStarStructure (multiMomentumS m w q) :=
  multiMomentumOSDiagonalKernelBounded w
    (fun r => (closure_forward_light_cone_subset (hq r)).1)

theorem multiMomentumOSContraction_of_mem_closure_forward_light_cone
    {m : ℕ} {w : Fin m → ℝ} (hw : ∀ r : Fin m, 0 ≤ w r)
    {q : Fin m → Fin 4 → ℝ}
    (hq : ∀ r : Fin m, q r ∈ closure forward_light_cone) :
    OSContractionCondition (multiMomentumOSData hw q) :=
  multiMomentumOSContraction hw
    (fun r => (closure_forward_light_cone_subset (hq r)).1)

theorem tendsto_osKernel_multiMomentumS_timeShift {m : ℕ} (w : Fin m → ℝ)
    {q : Fin m → Fin 4 → ℝ} (hq0 : ∀ r : Fin m, 0 < q r 0)
    (A B : OSConfig Unit) :
    Tendsto
      (fun τ : ℝ =>
        osKernel trivialStarStructure (multiMomentumS m w q) A
          (osConfigTimeShift (max τ 0) (le_max_right τ 0) B))
      atTop
      (𝓝 (∑ r : Fin m, (w r : ℂ) *
        (osKernel trivialStarStructure (fourMomentumS (q r)) A (osVacuumConfig Unit) *
          osKernel trivialStarStructure (fourMomentumS (q r)) (osVacuumConfig Unit) B))) := by
  have h_eq :
      (fun τ : ℝ =>
        osKernel trivialStarStructure (multiMomentumS m w q) A
          (osConfigTimeShift (max τ 0) (le_max_right τ 0) B)) =
      (fun τ : ℝ =>
        ∑ r : Fin m, (w r : ℂ) *
          osKernel trivialStarStructure (fourMomentumS (q r)) A
            (osConfigTimeShift (max τ 0) (le_max_right τ 0) B)) := by
    ext τ
    exact osKernel_multiMomentumS_eq m w q A (osConfigTimeShift (max τ 0) (le_max_right τ 0) B)
  rw [h_eq]
  refine tendsto_finsetSum Finset.univ (fun r _ => ?_)
  exact (fourMomentumOSTimeCluster (hq0 r) A B).const_mul (w r : ℂ)

theorem multiMomentum_master {m : ℕ} {w : Fin m → ℝ}
    (hw : ∀ r : Fin m, 0 ≤ w r) {q : Fin m → Fin 4 → ℝ}
    (hq : ∀ r : Fin m, q r ∈ closure forward_light_cone) :
    ForwardConeSpectrumCondition (multiMomentumW m w q) ∧
    Positivity trivialStarStructure (multiMomentumW m w q) ∧
    WightmanPCT 1 trivialRep (multiMomentumW m w q) ∧
    TubeTranslationInvariant (multiMomentumTubeExtension m w q) ∧
    TubeWickHermiticity trivialStarStructure (multiMomentumTubeExtension m w q) ∧
    TubeWeakLocality 1 (multiMomentumTubeExtension m w q) ∧
    (∀ (n : ℕ) (α : Fin n → Unit) (z : Fin n → Fin 4 → ℂ),
      z ∈ forward_tube_n n → ‖multiMomentumH m w q n α z‖ ≤ ∑ r : Fin m, w r) ∧
    OSTranslationInvariant (multiMomentumS m w q) ∧
    OSHermiticity trivialStarStructure (multiMomentumS m w q) ∧
    OSReflectionPositive trivialStarStructure (multiMomentumS m w q) ∧
    (OSVacuumNormalized (multiMomentumS m w q) ↔ ∑ r : Fin m, w r = 1) ∧
    OSDiagonalKernelBounded trivialStarStructure (multiMomentumS m w q) ∧
    OSContractionCondition (multiMomentumOSData hw q) :=
  ⟨multiMomentumW_forwardConeSpectrumCondition w hq,
   multiMomentumW_positivity hw q,
   multiMomentumW_pct m w q,
   multiMomentumTubeTranslationInvariant m w q,
   multiMomentumTubeWickHermiticity m w q,
   multiMomentumTubeWeakLocality_one m w q,
   fun n α _z hz => norm_multiMomentumH_le_sum hw hq n α hz,
   multiMomentumOSTranslationInvariant m w q,
   multiMomentumOSHermiticity m w q,
   multiMomentumOSReflectionPositive hw q,
   multiMomentumS_vacuumNormalized_iff m w q,
   multiMomentumOSDiagonalKernelBounded_of_mem_closure_forward_light_cone w hq,
   multiMomentumOSContraction_of_mem_closure_forward_light_cone hw hq⟩

theorem multiMomentum_kallenLehmann_master {m : ℕ} {w E : Fin m → ℝ}
    (hw : ∀ r : Fin m, 0 ≤ w r) (hE : ∀ r : Fin m, 0 ≤ E r) :
    (∀ (α : Fin 2 → Unit) (z : Fin 2 → Fin 4 → ℂ),
      multiMomentumH m w (fun r => euclidTimeVec (E r)) 2 α z =
        discreteKallenLehmannTube m w E z) ∧
    (∀ (α : Fin 2 → Unit) (x : Fin 2 → Fin 4 → ℝ),
      multiMomentumS m w (fun r => euclidTimeVec (E r)) 2 α x =
        discreteKallenLehmannEuclid m w E x) ∧
    ForwardConeSpectrumCondition
      (multiMomentumW m w (fun r => euclidTimeVec (E r))) ∧
    Positivity trivialStarStructure
      (multiMomentumW m w (fun r => euclidTimeVec (E r))) ∧
    OSReflectionPositive trivialStarStructure
      (multiMomentumS m w (fun r => euclidTimeVec (E r))) ∧
    OSScalarRotInvariant
      (multiMomentumS m w (fun r => euclidTimeVec (E r))) ∧
    OSSpinorRotCovariant trivialRep
      (multiMomentumS m w (fun r => euclidTimeVec (E r))) ∧
    OSDiagonalKernelBounded trivialStarStructure
      (multiMomentumS m w (fun r => euclidTimeVec (E r))) ∧
    OSContractionCondition
      (multiMomentumOSData hw (fun r => euclidTimeVec (E r))) := by
  have hq : ∀ r : Fin m, euclidTimeVec (E r) ∈ closure forward_light_cone :=
    fun r => euclidTimeVec_mem_closure_forward_light_cone (hE r)
  exact ⟨multiMomentumH_two_euclidTimeVec m w E,
   multiMomentumS_two_euclidTimeVec m w E,
   multiMomentumW_forwardConeSpectrumCondition w hq,
   multiMomentumW_positivity hw (fun r => euclidTimeVec (E r)),
   multiMomentumOSReflectionPositive hw (fun r => euclidTimeVec (E r)),
   osScalarRotInvariant_multiMomentumS_euclidTimeVec m w E,
   osSpinorRotCovariant_multiMomentumS_euclidTimeVec m w E,
   multiMomentumOSDiagonalKernelBounded_of_mem_closure_forward_light_cone w hq,
   multiMomentumOSContraction_of_mem_closure_forward_light_cone hw hq⟩

lemma fourMomentumW_odd_eq_zero (q : Fin 4 → ℝ) {n : ℕ} (hn : n % 2 = 1)
    (α : Fin n → Unit) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    fourMomentumW q n α f = 0 := by
  have hne : ¬ n % 2 = 0 := by omega
  rw [fourMomentumW_apply, if_neg hne]

lemma fourMomentumH_odd_eq_zero (q : Fin 4 → ℝ) {n : ℕ} (hn : n % 2 = 1)
    (α : Fin n → Unit) (z : Fin n → Fin 4 → ℂ) :
    fourMomentumH q n α z = 0 := by
  have hne : ¬ n % 2 = 0 := by omega
  unfold fourMomentumH
  rw [if_neg hne]

lemma fourMomentumS_odd_eq_zero (q : Fin 4 → ℝ) {n : ℕ} (hn : n % 2 = 1)
    (α : Fin n → Unit) (x : Fin n → Fin 4 → ℝ) :
    fourMomentumS q n α x = 0 :=
  fourMomentumH_odd_eq_zero q hn α (wickEmbedN n x)

theorem star_fourMomentumH_eq (q : Fin 4 → ℝ) (n : ℕ) (α : Fin n → Unit)
    (z : Fin n → Fin 4 → ℂ) :
    star (fourMomentumH q n α z) =
      fourMomentumH q n α (fun i μ => star (z (Fin.rev i) μ)) := by
  unfold fourMomentumH
  by_cases hn : n % 2 = 0
  · rw [if_pos hn, if_pos hn, star_vladimirov_kernel_eq]
    congr 1
    ext i μ
    rw [alternatingMomentum_rev_of_even n hn q i, Pi.neg_apply, Pi.neg_apply, neg_neg]
  · simp [hn]

theorem fourMomentumW_pct_scalar (q : Fin 4 → ℝ) (n : ℕ) (α : Fin n → Unit)
    {f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ}
    (hf' : ∀ x : Fin n → Fin 4 → ℝ, f' (fun i => -x (Fin.rev i)) = f x) :
    fourMomentumW q n α f = fourMomentumW q n α f' := by
  have hpct := wightman_pct_scalar_of_tubeWeakLocality (fourMomentumTubeExtension q)
    (fourMomentumTubeTranslationInvariant q) (fourMomentumTubeWeakLocality_one q)
    n α f f' hf'
  have hα : α ∘ Fin.rev = α := Subsingleton.elim _ _
  simpa [hα] using hpct

noncomputable def coeffMomentumW (C : ∀ n : ℕ, (Fin n → ι) → ℂ)
    (q : Fin 4 → ℝ) : WightmanFamily ι :=
  fun n α => C n α • fourMomentumW q n default

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma coeffMomentumW_apply (C : ∀ n : ℕ, (Fin n → ι) → ℂ) (q : Fin 4 → ℝ)
    (n : ℕ) (α : Fin n → ι) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    coeffMomentumW C q n α f = C n α * fourMomentumW q n default f := by
  change (C n α • fourMomentumW q n default) f = _
  rw [_root_.smul_apply, smul_eq_mul]

noncomputable def coeffMomentumH (C : ∀ n : ℕ, (Fin n → ι) → ℂ)
    (q : Fin 4 → ℝ) (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ) : ℂ :=
  C n α * fourMomentumH q n default z

omit [Fintype ι] [DecidableEq ι] in
theorem analyticAt_coeffMomentumH (C : ∀ n : ℕ, (Fin n → ι) → ℂ)
    (q : Fin 4 → ℝ) (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ) :
    AnalyticAt ℂ (coeffMomentumH C q n α) z :=
  analyticAt_const.mul (analyticAt_fourMomentumH q n default z)

omit [Fintype ι] [DecidableEq ι] in
theorem analyticOnNhd_coeffMomentumH (C : ∀ n : ℕ, (Fin n → ι) → ℂ)
    (q : Fin 4 → ℝ) (n : ℕ) (α : Fin n → ι) (s : Set (Fin n → Fin 4 → ℂ)) :
    AnalyticOnNhd ℂ (coeffMomentumH C q n α) s :=
  fun z _ => analyticAt_coeffMomentumH C q n α z

omit [Fintype ι] [DecidableEq ι] in
theorem analyticOn_coeffMomentumH (C : ∀ n : ℕ, (Fin n → ι) → ℂ)
    (q : Fin 4 → ℝ) (n : ℕ) (α : Fin n → ι) (s : Set (Fin n → Fin 4 → ℂ)) :
    AnalyticOn ℂ (coeffMomentumH C q n α) s :=
  (analyticOnNhd_coeffMomentumH C q n α s).analyticOn

omit [Fintype ι] [DecidableEq ι] in
noncomputable def coeffMomentumTubeExtension (C : ∀ n : ℕ, (Fin n → ι) → ℂ)
    (q : Fin 4 → ℝ) : TubeExtension (coeffMomentumW C q) where
  H := coeffMomentumH C q
  analytic n α := analyticOn_coeffMomentumH C q n α (forward_tube_n n)
  boundary n α f v hv := by
    have h_eq :
        (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
          coeffMomentumH C q n α
            (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x) =
          fun t : ℝ =>
            C n α * ∫ x : Fin n → Fin 4 → ℝ,
              fourMomentumH q n default
                (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x := by
      ext t
      unfold coeffMomentumH
      simp_rw [mul_assoc]
      exact integral_const_mul (C n α) _
    rw [h_eq, coeffMomentumW_apply]
    exact ((fourMomentumTubeExtension q).boundary n default f v hv).const_mul (C n α)

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma coeffMomentumTubeExtension_H (C : ∀ n : ℕ, (Fin n → ι) → ℂ) (q : Fin 4 → ℝ) :
    (coeffMomentumTubeExtension C q).H = coeffMomentumH C q := rfl

noncomputable def coeffMomentumS (C : ∀ n : ℕ, (Fin n → ι) → ℂ)
    (q : Fin 4 → ℝ) : SchwingerFamily ι :=
  schwingerFromTube (coeffMomentumTubeExtension C q)

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma coeffMomentumS_apply (C : ∀ n : ℕ, (Fin n → ι) → ℂ)
    (q : Fin 4 → ℝ) (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ) :
    coeffMomentumS C q n α x = C n α * fourMomentumS q n default x := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma coeffMomentumH_zero (C : ∀ n : ℕ, (Fin n → ι) → ℂ)
    (q : Fin 4 → ℝ) (α : Fin 0 → ι) (z : Fin 0 → Fin 4 → ℂ) :
    coeffMomentumH C q 0 α z = C 0 α := by
  simp [coeffMomentumH]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma coeffMomentumS_zero (C : ∀ n : ℕ, (Fin n → ι) → ℂ)
    (q : Fin 4 → ℝ) (α : Fin 0 → ι) (x : Fin 0 → Fin 4 → ℝ) :
    coeffMomentumS C q 0 α x = C 0 α := by
  simp [coeffMomentumS_apply]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma coeffMomentumH_two_euclidTimeVec (C : ∀ n : ℕ, (Fin n → ι) → ℂ)
    (E : ℝ) (α : Fin 2 → ι) (z : Fin 2 → Fin 4 → ℂ) :
    coeffMomentumH C (euclidTimeVec E) 2 α z =
      C 2 α * spectralTwoPointTube E z := by
  rw [coeffMomentumH, fourMomentumH_two_euclidTimeVec]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma coeffMomentumS_two_euclidTimeVec (C : ∀ n : ℕ, (Fin n → ι) → ℂ)
    (E : ℝ) (α : Fin 2 → ι) (x : Fin 2 → Fin 4 → ℝ) :
    coeffMomentumS C (euclidTimeVec E) 2 α x =
      C 2 α * euclidSpectralTwoPoint E x := by
  rw [coeffMomentumS_apply, fourMomentumS_two_euclidTimeVec]

omit [Fintype ι] [DecidableEq ι] in
lemma coeffMomentumW_odd_eq_zero (C : ∀ n : ℕ, (Fin n → ι) → ℂ)
    (q : Fin 4 → ℝ) {n : ℕ} (hn : n % 2 = 1) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    coeffMomentumW C q n α f = 0 := by
  rw [coeffMomentumW_apply, fourMomentumW_odd_eq_zero q hn default f, mul_zero]

omit [Fintype ι] [DecidableEq ι] in
lemma coeffMomentumH_odd_eq_zero (C : ∀ n : ℕ, (Fin n → ι) → ℂ)
    (q : Fin 4 → ℝ) {n : ℕ} (hn : n % 2 = 1) (α : Fin n → ι)
    (z : Fin n → Fin 4 → ℂ) :
    coeffMomentumH C q n α z = 0 := by
  rw [coeffMomentumH, fourMomentumH_odd_eq_zero q hn default z, mul_zero]

omit [Fintype ι] [DecidableEq ι] in
lemma coeffMomentumS_odd_eq_zero (C : ∀ n : ℕ, (Fin n → ι) → ℂ)
    (q : Fin 4 → ℝ) {n : ℕ} (hn : n % 2 = 1) (α : Fin n → ι)
    (x : Fin n → Fin 4 → ℝ) :
    coeffMomentumS C q n α x = 0 := by
  rw [coeffMomentumS_apply, fourMomentumS_odd_eq_zero q hn default x, mul_zero]

omit [Fintype ι] [DecidableEq ι] in
theorem coeffMomentumTubeTranslationInvariant (C : ∀ n : ℕ, (Fin n → ι) → ℂ)
    (q : Fin 4 → ℝ) :
    TubeTranslationInvariant (coeffMomentumTubeExtension C q) := by
  intro n α z a hz
  change coeffMomentumH C q n α (fun i => z i + a) = coeffMomentumH C q n α z
  unfold coeffMomentumH
  have h4 : fourMomentumH q n default (fun i => z i + a) =
      fourMomentumH q n default z :=
    fourMomentumTubeTranslationInvariant q n default z a hz
  rw [h4]

omit [Fintype ι] [DecidableEq ι] in
theorem coeffMomentumOSTranslationInvariant (C : ∀ n : ℕ, (Fin n → ι) → ℂ)
    (q : Fin 4 → ℝ) :
    OSTranslationInvariant (coeffMomentumS C q) :=
  schwingerFromTube_translation_invariant (coeffMomentumTubeExtension C q)
    (coeffMomentumTubeTranslationInvariant C q)

omit [Fintype ι] [DecidableEq ι] in
theorem coeffMomentumW_translationInvariant (C : ∀ n : ℕ, (Fin n → ι) → ℂ)
    (q : Fin 4 → ℝ) (n : ℕ) (α : Fin n → ι) (a : Fin 4 → ℝ)
    (f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hf' : ∀ x : Fin n → Fin 4 → ℝ, f' (fun i => x i + a) = f x) :
    coeffMomentumW C q n α f' = coeffMomentumW C q n α f :=
  wightman_translationInvariant_of_tubeTranslationInvariant
    (coeffMomentumTubeExtension C q) (coeffMomentumTubeTranslationInvariant C q)
    n α a f f' hf'

omit [Fintype ι] [DecidableEq ι] in
theorem coeffMomentumS_contDiffOn (C : ∀ n : ℕ, (Fin n → ι) → ℂ)
    (q : Fin 4 → ℝ) (n : ℕ) (α : Fin n → ι) :
    ContDiffOn ℝ (⊤ : ℕ∞) (coeffMomentumS C q n α) (orderedEuclidN n) :=
  schwingerFromTube_contDiffOn (coeffMomentumTubeExtension C q) n α

theorem coeffMomentumTubeWickHermiticity {R : HolomorphicLorentzRep ι}
    (S : StarStructure R) {C : ∀ n : ℕ, (Fin n → ι) → ℂ}
    (hC : ∀ (n : ℕ) (α : Fin n → ι),
      (∑ β : Fin n → ι, (∏ i : Fin n, S.C (α i) (β i)) * C n (β ∘ Fin.rev)) =
        star (C n α))
    (q : Fin 4 → ℝ) :
    TubeWickHermiticity S (coeffMomentumTubeExtension C q) := by
  intro n α z _hz _hstar
  have h_sum : ∀ β : Fin n → ι,
      (∏ i : Fin n, S.C (α i) (β i)) *
        (coeffMomentumTubeExtension C q).H n (β ∘ Fin.rev)
          (fun i μ => star (z (Fin.rev i) μ)) =
      ((∏ i : Fin n, S.C (α i) (β i)) * C n (β ∘ Fin.rev)) *
        fourMomentumH q n default (fun i μ => star (z (Fin.rev i) μ)) := by
    intro β
    rw [coeffMomentumTubeExtension_H, coeffMomentumH, mul_assoc]
  simp_rw [h_sum, ← Finset.sum_mul, hC n α, coeffMomentumTubeExtension_H,
    coeffMomentumH, star_mul', star_fourMomentumH_eq]

theorem coeffMomentumOSHermiticity {R : HolomorphicLorentzRep ι}
    (S : StarStructure R) {C : ∀ n : ℕ, (Fin n → ι) → ℂ}
    (hC : ∀ (n : ℕ) (α : Fin n → ι),
      (∑ β : Fin n → ι, (∏ i : Fin n, S.C (α i) (β i)) * C n (β ∘ Fin.rev)) =
        star (C n α))
    (q : Fin 4 → ℝ) :
    OSHermiticity S (coeffMomentumS C q) :=
  schwingerFromTube_os_hermiticity S (coeffMomentumTubeExtension C q)
    (coeffMomentumTubeWickHermiticity S hC q)

omit [Fintype ι] [DecidableEq ι] in
theorem coeffMomentumTubeWeakLocality {C : ∀ n : ℕ, (Fin n → ι) → ℂ} {η : ℂ}
    (hC : ∀ (n : ℕ) (α : Fin n → ι),
      C n α = η ^ (n * (n - 1) / 2) * C n (α ∘ Fin.rev))
    (q : Fin 4 → ℝ) :
    TubeWeakLocality η (coeffMomentumTubeExtension C q) := by
  intro n α z hz
  change coeffMomentumH C q n α (-(z ∘ Fin.rev)) =
    η ^ (n * (n - 1) / 2) * coeffMomentumH C q n (α ∘ Fin.rev) z
  unfold coeffMomentumH
  have h4 := fourMomentumTubeWeakLocality_one q n default z hz
  change fourMomentumH q n default (-(z ∘ Fin.rev)) =
    (1 : ℂ) ^ (n * (n - 1) / 2) *
      fourMomentumH q n (default ∘ Fin.rev) z at h4
  have hdef : (default : Fin n → Unit) ∘ Fin.rev = default := Subsingleton.elim _ _
  rw [one_pow, one_mul, hdef] at h4
  rw [h4, hC n α, mul_assoc]

omit [Fintype ι] [DecidableEq ι] in
theorem coeffMomentumOSSymmetric {C : ∀ n : ℕ, (Fin n → ι) → ℂ} {η : ℂ}
    (hC : ∀ (n : ℕ) (α : Fin n → ι),
      C n α = η ^ (n * (n - 1) / 2) * C n (α ∘ Fin.rev))
    (q : Fin 4 → ℝ) (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ)
    (hx : x ∈ orderedEuclidN n) :
    coeffMomentumS C q n α (-(x ∘ Fin.rev)) =
      η ^ (n * (n - 1) / 2) * coeffMomentumS C q n (α ∘ Fin.rev) x :=
  schwingerFromTube_weakLocality (coeffMomentumTubeExtension C q)
    (coeffMomentumTubeWeakLocality hC q) n α x hx

theorem coeffMomentumW_pct_of_sum_sigma (R : HolomorphicLorentzRep ι)
    {C : ∀ n : ℕ, (Fin n → ι) → ℂ} {η : ℂ}
    (hC_loc : ∀ (n : ℕ) (α : Fin n → ι),
      C n α = η ^ (n * (n - 1) / 2) * C n (α ∘ Fin.rev))
    (hC_pt : ∀ (n : ℕ) (α : Fin n → ι),
      (∑ β : Fin n → ι, (∏ i : Fin n, R.σ (-1, 1) (α i) (β i)) * C n β) = C n α)
    (q : Fin 4 → ℝ) :
    WightmanPCT η R (coeffMomentumW C q) := by
  intro n α f f' hf'
  rw [coeffMomentumW_apply, fourMomentumW_pct_scalar q n default hf', hC_loc n α]
  have h_sum : ∀ β : Fin n → ι,
      (∏ i : Fin n, R.σ (-1, 1) (α i) (β i)) *
        coeffMomentumW C q n (β ∘ Fin.rev) f' =
      ((∏ i : Fin n, R.σ (-1, 1) (α i) (β i)) * C n (β ∘ Fin.rev)) *
        fourMomentumW q n default f' := by
    intro β
    rw [coeffMomentumW_apply, mul_assoc]
  simp_rw [h_sum, ← Finset.sum_mul,
    ← sum_prod_revIndex n (R.σ (-1, 1)) (C n) α, hC_pt n (α ∘ Fin.rev), mul_assoc]

theorem coeffMomentumW_pct_of_sigma_pt_eq_neg_one (R : HolomorphicLorentzRep ι)
    {C : ∀ n : ℕ, (Fin n → ι) → ℂ} {η : ℂ} {q : Fin 4 → ℝ}
    (hσ : R.σ (-1, 1) = (-1 : ℂ) • (1 : Matrix ι ι ℂ))
    (hloc : TubeWeakLocality η (coeffMomentumTubeExtension C q)) :
    WightmanPCT η R (coeffMomentumW C q) := by
  intro n α f f' hf'
  rw [sum_prod_sigma_pt_eq_of_smul_one hσ n α
    (fun β => coeffMomentumW C q n (β ∘ Fin.rev) f')]
  rcases Nat.even_or_odd n with hn | hn
  · rw [Even.neg_one_pow hn, one_mul]
    exact wightman_pct_scalar_of_tubeWeakLocality (coeffMomentumTubeExtension C q)
      (coeffMomentumTubeTranslationInvariant C q) hloc n α f f' hf'
  · have hodd : n % 2 = 1 := Nat.odd_iff.mp hn
    rw [coeffMomentumW_odd_eq_zero C q hodd α f,
        coeffMomentumW_odd_eq_zero C q hodd (α ∘ Fin.rev) f',
        mul_zero, mul_zero]

omit [Fintype ι] [DecidableEq ι] in
theorem coeffMomentumW_forwardConeSpectrumCondition
    (C : ∀ n : ℕ, (Fin n → ι) → ℂ) {q : Fin 4 → ℝ}
    (hq : q ∈ closure forward_light_cone) :
    ForwardConeSpectrumCondition (coeffMomentumW C q) := by
  intro n α f hf
  rw [coeffMomentumW_apply,
      fourMomentumW_forwardConeSpectrumCondition hq n default f hf, mul_zero]

omit [Fintype ι] [DecidableEq ι] in
theorem norm_coeffMomentumH_le (C : ∀ n : ℕ, (Fin n → ι) → ℂ)
    {q : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone)
    (n : ℕ) (α : Fin n → ι) {z : Fin n → Fin 4 → ℂ} (hz : z ∈ forward_tube_n n) :
    ‖coeffMomentumH C q n α z‖ ≤ ‖C n α‖ := by
  unfold coeffMomentumH
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (norm_fourMomentumH_le_one hq n default hz)

omit [Fintype ι] [DecidableEq ι] in
theorem osScalarRotInvariant_coeffMomentumS_euclidTimeVec
    (C : ∀ n : ℕ, (Fin n → ι) → ℂ) (E : ℝ) :
    OSScalarRotInvariant (coeffMomentumS C (euclidTimeVec E)) := by
  intro n U α x _hx
  rw [coeffMomentumS_apply, coeffMomentumS_apply,
      fourMomentumS_euclidTimeVec_euclidRotN_su2Conj E n U default x]

theorem osSpinorRotCovariant_coeffMomentumS_euclidTimeVec
    (R : HolomorphicLorentzRep ι) {C : ∀ n : ℕ, (Fin n → ι) → ℂ}
    (hC : ∀ (n : ℕ) (p : SL2C × SL2C) (α : Fin n → ι),
      (∑ β : Fin n → ι, (∏ i : Fin n, R.σ p (α i) (β i)) * C n β) = C n α)
    (E : ℝ) :
    OSSpinorRotCovariant R (coeffMomentumS C (euclidTimeVec E)) := by
  intro n U α x _hx
  have h_sum : ∀ β : Fin n → ι,
      (∏ i : Fin n, osSpinorRotMatrix R U (α i) (β i)) *
        coeffMomentumS C (euclidTimeVec E) n β x =
      ((∏ i : Fin n, R.σ (su2ToSL2C U, su2ToSL2C (su2Conj U)) (α i) (β i)) * C n β) *
        fourMomentumS (euclidTimeVec E) n default x := by
    intro β
    rw [coeffMomentumS_apply, mul_assoc]
    rfl
  simp_rw [h_sum, ← Finset.sum_mul,
    hC n (su2ToSL2C U, su2ToSL2C (su2Conj U)) α, coeffMomentumS_apply,
    fourMomentumS_euclidTimeVec_euclidRotN_su2Conj E n U default x]

lemma weylFermionConst_mul_z2FreeCoeff (n : ℕ) (α : Fin n → Fin 2) :
    weylFermionConst n α * z2FreeCoeff n = weylFermionConst n α := by
  match n with
  | 0 => simp [weylFermionConst, z2FreeCoeff_eq_ite]
  | 1 => simp [weylFermionConst]
  | 2 => simp [weylFermionConst, z2FreeCoeff_eq_ite]
  | m + 3 => simp [weylFermionConst]

lemma norm_weylEpsilon_le_one (α : Fin 2 → Fin 2) :
    ‖weylEpsilon α‖ ≤ 1 := by
  rw [finTwo_eq_vecCons α]
  generalize α 0 = a
  generalize α 1 = b
  fin_cases a <;> fin_cases b <;>
    simp [weylEpsilon_zero_zero, weylEpsilon_zero_one,
          weylEpsilon_one_zero, weylEpsilon_one_one]

lemma norm_weylFermionConst_le_one (n : ℕ) (α : Fin n → Fin 2) :
    ‖weylFermionConst n α‖ ≤ 1 := by
  match n with
  | 0 => simp [weylFermionConst]
  | 1 => simp [weylFermionConst]
  | 2 => exact norm_weylEpsilon_le_one α
  | m + 3 => simp [weylFermionConst]

noncomputable def weylMomentumW (q : Fin 4 → ℝ) : WightmanFamily (Fin 2) :=
  coeffMomentumW weylFermionConst q

noncomputable def weylMomentumH (q : Fin 4 → ℝ) :
    ∀ n : ℕ, (Fin n → Fin 2) → (Fin n → Fin 4 → ℂ) → ℂ :=
  coeffMomentumH weylFermionConst q

noncomputable def weylMomentumTubeExtension (q : Fin 4 → ℝ) :
    TubeExtension (weylMomentumW q) :=
  coeffMomentumTubeExtension weylFermionConst q

noncomputable def weylMomentumS (q : Fin 4 → ℝ) : SchwingerFamily (Fin 2) :=
  coeffMomentumS weylFermionConst q

@[simp]
lemma weylMomentumTubeExtension_H (q : Fin 4 → ℝ) :
    (weylMomentumTubeExtension q).H = weylMomentumH q := rfl

@[simp]
lemma weylMomentumW_apply (q : Fin 4 → ℝ) (n : ℕ) (α : Fin n → Fin 2)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    weylMomentumW q n α f = weylFermionConst n α * fourMomentumW q n default f :=
  coeffMomentumW_apply weylFermionConst q n α f

@[simp]
lemma weylMomentumH_apply (q : Fin 4 → ℝ) (n : ℕ) (α : Fin n → Fin 2)
    (z : Fin n → Fin 4 → ℂ) :
    weylMomentumH q n α z = weylFermionConst n α * fourMomentumH q n default z := rfl

@[simp]
lemma weylMomentumS_apply (q : Fin 4 → ℝ) (n : ℕ) (α : Fin n → Fin 2)
    (x : Fin n → Fin 4 → ℝ) :
    weylMomentumS q n α x = weylFermionConst n α * fourMomentumS q n default x := rfl

@[simp]
theorem weylMomentumW_zero_momentum : weylMomentumW 0 = weylFermionW := by
  ext n α f
  rw [weylMomentumW_apply, fourMomentumW_zero_momentum_eq]
  change weylFermionConst n α * momentW z2FreeCoeff n default f = weylFermionW n α f
  rw [momentW_apply, weylFermionW_apply, ← mul_assoc, weylFermionConst_mul_z2FreeCoeff]

@[simp]
theorem weylMomentumH_zero_momentum : weylMomentumH 0 = weylFermionH := by
  ext n α z
  change weylFermionConst n α * fourMomentumH 0 n default z = weylFermionConst n α
  rw [fourMomentumH_zero_momentum_eq, weylFermionConst_mul_z2FreeCoeff]

@[simp]
theorem weylMomentumS_zero_momentum : weylMomentumS 0 = weylFermionS := by
  ext n α x
  change weylFermionConst n α * fourMomentumS 0 n default x = weylFermionConst n α
  rw [fourMomentumS_zero_momentum_eq]
  change weylFermionConst n α * z2FreeCoeff n = weylFermionConst n α
  exact weylFermionConst_mul_z2FreeCoeff n α

@[simp]
theorem weylMomentumH_two_euclidTimeVec (E : ℝ) (α : Fin 2 → Fin 2)
    (z : Fin 2 → Fin 4 → ℂ) :
    weylMomentumH (euclidTimeVec E) 2 α z =
      weylEpsilon α * spectralTwoPointTube E z :=
  coeffMomentumH_two_euclidTimeVec weylFermionConst E α z

@[simp]
theorem weylMomentumS_two_euclidTimeVec (E : ℝ) (α : Fin 2 → Fin 2)
    (x : Fin 2 → Fin 4 → ℝ) :
    weylMomentumS (euclidTimeVec E) 2 α x =
      weylEpsilon α * euclidSpectralTwoPoint E x :=
  coeffMomentumS_two_euclidTimeVec weylFermionConst E α x

theorem weylMomentumS_two_base_ne_doubleBase {q : Fin 4 → ℝ} (hq0 : q 0 ≠ 0) :
    weylMomentumS q 2 ![0, 1] (euclidOrderedBasePoint 2) ≠
      weylMomentumS q 2 ![0, 1] euclidTwoPointDoubleBase := by
  rw [weylMomentumS_apply, weylMomentumS_apply, weylFermionConst_two,
      weylEpsilon_zero_one, one_mul, one_mul]
  exact fourMomentumS_two_base_ne_doubleBase hq0 default

theorem weylMomentumH_two_not_const {q : Fin 4 → ℝ} (hq0 : q 0 ≠ 0) :
    ∃ z₁ z₂ : Fin 2 → Fin 4 → ℂ,
      z₁ ∈ forward_tube_n 2 ∧ z₂ ∈ forward_tube_n 2 ∧
      weylMomentumH q 2 ![0, 1] z₁ ≠ weylMomentumH q 2 ![0, 1] z₂ := by
  refine ⟨wickEmbedN 2 (euclidOrderedBasePoint 2),
    wickEmbedN 2 euclidTwoPointDoubleBase,
    wickEmbedN_mem_forward_tube_n 2 (euclidOrderedBasePoint_mem_orderedEuclidN 2),
    wickEmbedN_mem_forward_tube_n 2 euclidTwoPointDoubleBase_mem_orderedEuclidN,
    weylMomentumS_two_base_ne_doubleBase hq0⟩

theorem weylMomentumTubeTranslationInvariant (q : Fin 4 → ℝ) :
    TubeTranslationInvariant (weylMomentumTubeExtension q) :=
  coeffMomentumTubeTranslationInvariant weylFermionConst q

theorem weylMomentumOSTranslationInvariant (q : Fin 4 → ℝ) :
    OSTranslationInvariant (weylMomentumS q) :=
  coeffMomentumOSTranslationInvariant weylFermionConst q

theorem weylMomentumW_translationInvariant (q : Fin 4 → ℝ)
    (n : ℕ) (α : Fin n → Fin 2) (a : Fin 4 → ℝ)
    (f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hf' : ∀ x : Fin n → Fin 4 → ℝ, f' (fun i => x i + a) = f x) :
    weylMomentumW q n α f' = weylMomentumW q n α f :=
  coeffMomentumW_translationInvariant weylFermionConst q n α a f f' hf'

theorem weylMomentumTubeWeakLocality (q : Fin 4 → ℝ) :
    TubeWeakLocality (-1) (weylMomentumTubeExtension q) :=
  coeffMomentumTubeWeakLocality weylFermionConst_eq_neg_one_pow_mul_rev q

theorem weylMomentumOSSymmetric (q : Fin 4 → ℝ)
    (n : ℕ) (α : Fin n → Fin 2) (x : Fin n → Fin 4 → ℝ)
    (hx : x ∈ orderedEuclidN n) :
    weylMomentumS q n α (-(x ∘ Fin.rev)) =
      (-1 : ℂ) ^ (n * (n - 1) / 2) * weylMomentumS q n (α ∘ Fin.rev) x :=
  coeffMomentumOSSymmetric weylFermionConst_eq_neg_one_pow_mul_rev q n α x hx

theorem weylFermionPCT :
    WightmanPCT (-1) leftWeylRep weylFermionW :=
  wightman_pct_leftWeylRep_of_tube weylFermionTubeExtension
    weylFermionTubeTranslationInvariant weylFermionTubeCovariant
    weylFermionTubeWeakLocality

theorem weylMomentumW_pct (q : Fin 4 → ℝ) :
    WightmanPCT (-1) leftWeylRep (weylMomentumW q) :=
  coeffMomentumW_pct_of_sum_sigma leftWeylRep
    weylFermionConst_eq_neg_one_pow_mul_rev
    (fun n α => sum_leftWeylRep_mul_weylFermionConst n (-1, 1) α) q

theorem weylMomentumW_forwardConeSpectrumCondition {q : Fin 4 → ℝ}
    (hq : q ∈ closure forward_light_cone) :
    ForwardConeSpectrumCondition (weylMomentumW q) :=
  coeffMomentumW_forwardConeSpectrumCondition weylFermionConst hq

theorem norm_weylMomentumH_le_one {q : Fin 4 → ℝ}
    (hq : q ∈ closure forward_light_cone) (n : ℕ) (α : Fin n → Fin 2)
    {z : Fin n → Fin 4 → ℂ} (hz : z ∈ forward_tube_n n) :
    ‖weylMomentumH q n α z‖ ≤ 1 :=
  (norm_coeffMomentumH_le weylFermionConst hq n α hz).trans
    (norm_weylFermionConst_le_one n α)

theorem osScalarRotInvariant_weylMomentumS_euclidTimeVec (E : ℝ) :
    OSScalarRotInvariant (weylMomentumS (euclidTimeVec E)) :=
  osScalarRotInvariant_coeffMomentumS_euclidTimeVec weylFermionConst E

theorem osSpinorRotCovariant_weylMomentumS_euclidTimeVec (E : ℝ) :
    OSSpinorRotCovariant leftWeylRep (weylMomentumS (euclidTimeVec E)) :=
  osSpinorRotCovariant_coeffMomentumS_euclidTimeVec leftWeylRep
    sum_leftWeylRep_mul_weylFermionConst E

theorem weylMomentum_master {E : ℝ} (hE : 0 ≤ E) :
    (∀ (α : Fin 2 → Fin 2) (z : Fin 2 → Fin 4 → ℂ),
      weylMomentumH (euclidTimeVec E) 2 α z =
        weylEpsilon α * spectralTwoPointTube E z) ∧
    (∀ (α : Fin 2 → Fin 2) (x : Fin 2 → Fin 4 → ℝ),
      weylMomentumS (euclidTimeVec E) 2 α x =
        weylEpsilon α * euclidSpectralTwoPoint E x) ∧
    TubeTranslationInvariant (weylMomentumTubeExtension (euclidTimeVec E)) ∧
    OSTranslationInvariant (weylMomentumS (euclidTimeVec E)) ∧
    TubeWeakLocality (-1) (weylMomentumTubeExtension (euclidTimeVec E)) ∧
    WightmanPCT (-1) leftWeylRep (weylMomentumW (euclidTimeVec E)) ∧
    ForwardConeSpectrumCondition (weylMomentumW (euclidTimeVec E)) ∧
    (∀ (n : ℕ) (α : Fin n → Fin 2) (z : Fin n → Fin 4 → ℂ),
      z ∈ forward_tube_n n → ‖weylMomentumH (euclidTimeVec E) n α z‖ ≤ 1) ∧
    OSScalarRotInvariant (weylMomentumS (euclidTimeVec E)) ∧
    OSSpinorRotCovariant leftWeylRep (weylMomentumS (euclidTimeVec E)) := by
  have hq : euclidTimeVec E ∈ closure forward_light_cone :=
    euclidTimeVec_mem_closure_forward_light_cone hE
  exact ⟨weylMomentumH_two_euclidTimeVec E,
    weylMomentumS_two_euclidTimeVec E,
    weylMomentumTubeTranslationInvariant (euclidTimeVec E),
    weylMomentumOSTranslationInvariant (euclidTimeVec E),
    weylMomentumTubeWeakLocality (euclidTimeVec E),
    weylMomentumW_pct (euclidTimeVec E),
    weylMomentumW_forwardConeSpectrumCondition hq,
    fun n α z hz => norm_weylMomentumH_le_one hq n α hz,
    osScalarRotInvariant_weylMomentumS_euclidTimeVec E,
    osSpinorRotCovariant_weylMomentumS_euclidTimeVec E⟩

lemma diracFermionConst_mul_z2FreeCoeff (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) :
    diracFermionConst n α * z2FreeCoeff n = diracFermionConst n α := by
  match n with
  | 0 => simp [diracFermionConst, z2FreeCoeff_eq_ite]
  | 1 => simp [diracFermionConst]
  | 2 => simp [diracFermionConst, z2FreeCoeff_eq_ite]
  | m + 3 => simp [diracFermionConst]

lemma norm_diracEpsilon_le_one (α : Fin 2 → Fin 2 ⊕ Fin 2) :
    ‖diracEpsilon α‖ ≤ 1 := by
  unfold diracEpsilon
  rcases α 0 with i | i <;> rcases α 1 with j | j <;>
    simp only [Complex.norm_mul, Complex.norm_I, one_mul, norm_zero, zero_le_one]
  · exact norm_weylEpsilon_le_one ![i, j]
  · exact norm_weylEpsilon_le_one ![i, j]

lemma norm_diracFermionConst_le_one (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) :
    ‖diracFermionConst n α‖ ≤ 1 := by
  match n with
  | 0 => simp [diracFermionConst]
  | 1 => simp [diracFermionConst]
  | 2 => exact norm_diracEpsilon_le_one α
  | m + 3 => simp [diracFermionConst]

lemma sum_prod_diracStarStructure_C_mul_diracFermionConst
    (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) :
    (∑ β : Fin n → Fin 2 ⊕ Fin 2,
      (∏ i : Fin n, diracStarStructure.C (α i) (β i)) *
        diracFermionConst n (β ∘ Fin.rev)) =
      star (diracFermionConst n α) := by
  dsimp [diracStarStructure]
  rw [sum_prod_chiralDoubleStarStructure_C_mul leftWeylRep leftWeylRep_hasRealConj
      n α (fun β => diracFermionConst n (β ∘ Fin.rev))]
  exact (star_diracFermionConst n α).symm

noncomputable def diracMomentumW (q : Fin 4 → ℝ) : WightmanFamily (Fin 2 ⊕ Fin 2) :=
  coeffMomentumW diracFermionConst q

noncomputable def diracMomentumH (q : Fin 4 → ℝ) :
    ∀ n : ℕ, (Fin n → Fin 2 ⊕ Fin 2) → (Fin n → Fin 4 → ℂ) → ℂ :=
  coeffMomentumH diracFermionConst q

noncomputable def diracMomentumTubeExtension (q : Fin 4 → ℝ) :
    TubeExtension (diracMomentumW q) :=
  coeffMomentumTubeExtension diracFermionConst q

noncomputable def diracMomentumS (q : Fin 4 → ℝ) : SchwingerFamily (Fin 2 ⊕ Fin 2) :=
  coeffMomentumS diracFermionConst q

@[simp]
lemma diracMomentumTubeExtension_H (q : Fin 4 → ℝ) :
    (diracMomentumTubeExtension q).H = diracMomentumH q := rfl

@[simp]
lemma diracMomentumW_apply (q : Fin 4 → ℝ) (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    diracMomentumW q n α f = diracFermionConst n α * fourMomentumW q n default f :=
  coeffMomentumW_apply diracFermionConst q n α f

@[simp]
lemma diracMomentumH_apply (q : Fin 4 → ℝ) (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2)
    (z : Fin n → Fin 4 → ℂ) :
    diracMomentumH q n α z = diracFermionConst n α * fourMomentumH q n default z := rfl

@[simp]
lemma diracMomentumS_apply (q : Fin 4 → ℝ) (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2)
    (x : Fin n → Fin 4 → ℝ) :
    diracMomentumS q n α x = diracFermionConst n α * fourMomentumS q n default x := rfl

@[simp]
theorem diracMomentumW_zero_momentum : diracMomentumW 0 = diracFermionW := by
  ext n α f
  rw [diracMomentumW_apply, fourMomentumW_zero_momentum_eq]
  change diracFermionConst n α * momentW z2FreeCoeff n default f = diracFermionW n α f
  rw [momentW_apply, diracFermionW_apply, ← mul_assoc, diracFermionConst_mul_z2FreeCoeff]

@[simp]
theorem diracMomentumH_zero_momentum : diracMomentumH 0 = diracFermionH := by
  ext n α z
  change diracFermionConst n α * fourMomentumH 0 n default z = diracFermionConst n α
  rw [fourMomentumH_zero_momentum_eq, diracFermionConst_mul_z2FreeCoeff]

@[simp]
theorem diracMomentumS_zero_momentum : diracMomentumS 0 = diracFermionS := by
  ext n α x
  change diracFermionConst n α * fourMomentumS 0 n default x = diracFermionConst n α
  rw [fourMomentumS_zero_momentum_eq]
  change diracFermionConst n α * z2FreeCoeff n = diracFermionConst n α
  exact diracFermionConst_mul_z2FreeCoeff n α

@[simp]
theorem diracMomentumH_two_euclidTimeVec (E : ℝ) (α : Fin 2 → Fin 2 ⊕ Fin 2)
    (z : Fin 2 → Fin 4 → ℂ) :
    diracMomentumH (euclidTimeVec E) 2 α z =
      diracEpsilon α * spectralTwoPointTube E z :=
  coeffMomentumH_two_euclidTimeVec diracFermionConst E α z

@[simp]
theorem diracMomentumS_two_euclidTimeVec (E : ℝ) (α : Fin 2 → Fin 2 ⊕ Fin 2)
    (x : Fin 2 → Fin 4 → ℝ) :
    diracMomentumS (euclidTimeVec E) 2 α x =
      diracEpsilon α * euclidSpectralTwoPoint E x :=
  coeffMomentumS_two_euclidTimeVec diracFermionConst E α x

theorem diracMomentumS_two_base_ne_doubleBase {q : Fin 4 → ℝ} (hq0 : q 0 ≠ 0) :
    diracMomentumS q 2 ![Sum.inl 0, Sum.inl 1] (euclidOrderedBasePoint 2) ≠
      diracMomentumS q 2 ![Sum.inl 0, Sum.inl 1] euclidTwoPointDoubleBase := by
  rw [diracMomentumS_apply, diracMomentumS_apply, diracFermionConst_two,
      diracEpsilon_inl_inl, weylEpsilon_zero_one, mul_one]
  intro h_eq
  exact fourMomentumS_two_base_ne_doubleBase hq0 default
    (mul_left_cancel₀ Complex.I_ne_zero h_eq)

theorem diracMomentumH_two_not_const {q : Fin 4 → ℝ} (hq0 : q 0 ≠ 0) :
    ∃ z₁ z₂ : Fin 2 → Fin 4 → ℂ,
      z₁ ∈ forward_tube_n 2 ∧ z₂ ∈ forward_tube_n 2 ∧
      diracMomentumH q 2 ![Sum.inl 0, Sum.inl 1] z₁ ≠
        diracMomentumH q 2 ![Sum.inl 0, Sum.inl 1] z₂ := by
  refine ⟨wickEmbedN 2 (euclidOrderedBasePoint 2),
    wickEmbedN 2 euclidTwoPointDoubleBase,
    wickEmbedN_mem_forward_tube_n 2 (euclidOrderedBasePoint_mem_orderedEuclidN 2),
    wickEmbedN_mem_forward_tube_n 2 euclidTwoPointDoubleBase_mem_orderedEuclidN,
    diracMomentumS_two_base_ne_doubleBase hq0⟩

theorem diracMomentumTubeTranslationInvariant (q : Fin 4 → ℝ) :
    TubeTranslationInvariant (diracMomentumTubeExtension q) :=
  coeffMomentumTubeTranslationInvariant diracFermionConst q

theorem diracMomentumOSTranslationInvariant (q : Fin 4 → ℝ) :
    OSTranslationInvariant (diracMomentumS q) :=
  coeffMomentumOSTranslationInvariant diracFermionConst q

theorem diracMomentumW_translationInvariant (q : Fin 4 → ℝ)
    (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) (a : Fin 4 → ℝ)
    (f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hf' : ∀ x : Fin n → Fin 4 → ℝ, f' (fun i => x i + a) = f x) :
    diracMomentumW q n α f' = diracMomentumW q n α f :=
  coeffMomentumW_translationInvariant diracFermionConst q n α a f f' hf'

theorem diracMomentumTubeWickHermiticity (q : Fin 4 → ℝ) :
    TubeWickHermiticity diracStarStructure (diracMomentumTubeExtension q) :=
  coeffMomentumTubeWickHermiticity diracStarStructure
    sum_prod_diracStarStructure_C_mul_diracFermionConst q

theorem diracMomentumOSHermiticity (q : Fin 4 → ℝ) :
    OSHermiticity diracStarStructure (diracMomentumS q) :=
  coeffMomentumOSHermiticity diracStarStructure
    sum_prod_diracStarStructure_C_mul_diracFermionConst q

theorem diracMomentumTubeWeakLocality (q : Fin 4 → ℝ) :
    TubeWeakLocality (-1) (diracMomentumTubeExtension q) :=
  coeffMomentumTubeWeakLocality diracFermionConst_eq_neg_one_pow_mul_rev q

theorem diracMomentumOSSymmetric (q : Fin 4 → ℝ)
    (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) (x : Fin n → Fin 4 → ℝ)
    (hx : x ∈ orderedEuclidN n) :
    diracMomentumS q n α (-(x ∘ Fin.rev)) =
      (-1 : ℂ) ^ (n * (n - 1) / 2) * diracMomentumS q n (α ∘ Fin.rev) x :=
  coeffMomentumOSSymmetric diracFermionConst_eq_neg_one_pow_mul_rev q n α x hx

theorem diracMomentumW_pct (q : Fin 4 → ℝ) :
    WightmanPCT (-1) diracRep (diracMomentumW q) :=
  coeffMomentumW_pct_of_sum_sigma diracRep
    diracFermionConst_eq_neg_one_pow_mul_rev
    (fun n α => sum_diracRep_mul_diracFermionConst n (-1, 1) α) q

theorem diracMomentumW_forwardConeSpectrumCondition {q : Fin 4 → ℝ}
    (hq : q ∈ closure forward_light_cone) :
    ForwardConeSpectrumCondition (diracMomentumW q) :=
  coeffMomentumW_forwardConeSpectrumCondition diracFermionConst hq

theorem norm_diracMomentumH_le_one {q : Fin 4 → ℝ}
    (hq : q ∈ closure forward_light_cone) (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2)
    {z : Fin n → Fin 4 → ℂ} (hz : z ∈ forward_tube_n n) :
    ‖diracMomentumH q n α z‖ ≤ 1 :=
  (norm_coeffMomentumH_le diracFermionConst hq n α hz).trans
    (norm_diracFermionConst_le_one n α)

theorem osScalarRotInvariant_diracMomentumS_euclidTimeVec (E : ℝ) :
    OSScalarRotInvariant (diracMomentumS (euclidTimeVec E)) :=
  osScalarRotInvariant_coeffMomentumS_euclidTimeVec diracFermionConst E

theorem osSpinorRotCovariant_diracMomentumS_euclidTimeVec (E : ℝ) :
    OSSpinorRotCovariant diracRep (diracMomentumS (euclidTimeVec E)) :=
  osSpinorRotCovariant_coeffMomentumS_euclidTimeVec diracRep
    sum_diracRep_mul_diracFermionConst E

theorem diracMomentum_master {E : ℝ} (hE : 0 ≤ E) :
    (∀ (α : Fin 2 → Fin 2 ⊕ Fin 2) (z : Fin 2 → Fin 4 → ℂ),
      diracMomentumH (euclidTimeVec E) 2 α z =
        diracEpsilon α * spectralTwoPointTube E z) ∧
    (∀ (α : Fin 2 → Fin 2 ⊕ Fin 2) (x : Fin 2 → Fin 4 → ℝ),
      diracMomentumS (euclidTimeVec E) 2 α x =
        diracEpsilon α * euclidSpectralTwoPoint E x) ∧
    TubeTranslationInvariant (diracMomentumTubeExtension (euclidTimeVec E)) ∧
    OSTranslationInvariant (diracMomentumS (euclidTimeVec E)) ∧
    TubeWickHermiticity diracStarStructure
      (diracMomentumTubeExtension (euclidTimeVec E)) ∧
    OSHermiticity diracStarStructure (diracMomentumS (euclidTimeVec E)) ∧
    TubeWeakLocality (-1) (diracMomentumTubeExtension (euclidTimeVec E)) ∧
    WightmanPCT (-1) diracRep (diracMomentumW (euclidTimeVec E)) ∧
    ForwardConeSpectrumCondition (diracMomentumW (euclidTimeVec E)) ∧
    (∀ (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) (z : Fin n → Fin 4 → ℂ),
      z ∈ forward_tube_n n → ‖diracMomentumH (euclidTimeVec E) n α z‖ ≤ 1) ∧
    OSScalarRotInvariant (diracMomentumS (euclidTimeVec E)) ∧
    OSSpinorRotCovariant diracRep (diracMomentumS (euclidTimeVec E)) := by
  have hq : euclidTimeVec E ∈ closure forward_light_cone :=
    euclidTimeVec_mem_closure_forward_light_cone hE
  exact ⟨diracMomentumH_two_euclidTimeVec E,
    diracMomentumS_two_euclidTimeVec E,
    diracMomentumTubeTranslationInvariant (euclidTimeVec E),
    diracMomentumOSTranslationInvariant (euclidTimeVec E),
    diracMomentumTubeWickHermiticity (euclidTimeVec E),
    diracMomentumOSHermiticity (euclidTimeVec E),
    diracMomentumTubeWeakLocality (euclidTimeVec E),
    diracMomentumW_pct (euclidTimeVec E),
    diracMomentumW_forwardConeSpectrumCondition hq,
    fun n α z hz => norm_diracMomentumH_le_one hq n α hz,
    osScalarRotInvariant_diracMomentumS_euclidTimeVec E,
    osSpinorRotCovariant_diracMomentumS_euclidTimeVec E⟩

def vectorPolarizationFactor (e : Fin 4 → ℝ) (n : ℕ) (α : Fin n → Fin 4) : ℂ :=
  ∏ i : Fin n, (e (α i) : ℂ)

@[simp]
lemma vectorPolarizationFactor_zero (e : Fin 4 → ℝ) (α : Fin 0 → Fin 4) :
    vectorPolarizationFactor e 0 α = 1 := by
  simp [vectorPolarizationFactor]

@[simp]
lemma vectorPolarizationFactor_one (e : Fin 4 → ℝ) (α : Fin 1 → Fin 4) :
    vectorPolarizationFactor e 1 α = (e (α 0) : ℂ) := by
  simp [vectorPolarizationFactor]

@[simp]
lemma vectorPolarizationFactor_two (e : Fin 4 → ℝ) (α : Fin 2 → Fin 4) :
    vectorPolarizationFactor e 2 α = (e (α 0) : ℂ) * (e (α 1) : ℂ) := by
  simp [vectorPolarizationFactor, Fin.prod_univ_two]

@[simp]
lemma star_vectorPolarizationFactor (e : Fin 4 → ℝ) (n : ℕ) (α : Fin n → Fin 4) :
    star (vectorPolarizationFactor e n α) = vectorPolarizationFactor e n α := by
  unfold vectorPolarizationFactor
  rw [star_prod]
  refine Finset.prod_congr rfl (fun i _ => by simp)

@[simp]
lemma vectorPolarizationFactor_comp_rev (e : Fin 4 → ℝ) (n : ℕ) (α : Fin n → Fin 4) :
    vectorPolarizationFactor e n (α ∘ Fin.rev) = vectorPolarizationFactor e n α :=
  Equiv.prod_comp Fin.revPerm (fun i => (e (α i) : ℂ))

@[simp]
lemma vectorPolarizationFactor_append (e : Fin 4 → ℝ) (j k : ℕ)
    (α : Fin j → Fin 4) (α' : Fin k → Fin 4) :
    vectorPolarizationFactor e (j + k) (Fin.append α α') =
      vectorPolarizationFactor e j α * vectorPolarizationFactor e k α' := by
  unfold vectorPolarizationFactor
  rw [Fin.prod_univ_add]
  congr 1 <;> refine Finset.prod_congr rfl (fun i _ => ?_)
  · simp [Fin.append_left]
  · simp [Fin.append_right]

@[simp]
lemma vectorPolarizationFactor_osConcatIdx (e : Fin 4 → ℝ) (j k : ℕ)
    (α : Fin j → Fin 4) (α' : Fin k → Fin 4) :
    vectorPolarizationFactor e (j + k) (osConcatIdx j k α α') =
      vectorPolarizationFactor e j α * vectorPolarizationFactor e k α' := by
  unfold osConcatIdx
  rw [vectorPolarizationFactor_append, vectorPolarizationFactor_comp_rev]

lemma sum_prod_stdStarStructure_C_mul (n : ℕ) (α : Fin n → Fin 4)
    (F : (Fin n → Fin 4) → ℂ) :
    (∑ β : Fin n → Fin 4, (∏ i : Fin n, stdStarStructure.C (α i) (β i)) * F β) =
      F α := by
  have h_prod : ∀ β : Fin n → Fin 4,
      (∏ i : Fin n, stdStarStructure.C (α i) (β i)) =
        if α = β then 1 else 0 := by
    intro β
    change (∏ i : Fin n, (1 : Matrix (Fin 4) (Fin 4) ℂ) (α i) (β i)) =
      if α = β then 1 else 0
    by_cases h : α = β
    · subst h
      simp
    · rw [if_neg h]
      obtain ⟨i, hi⟩ : ∃ i, α i ≠ β i := by
        by_contra hc
        push Not at hc
        exact h (funext hc)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Matrix.one_apply_ne hi])
  simp_rw [h_prod, ite_mul, one_mul, zero_mul]
  simp

lemma sum_prod_stdStarStructure_C_mul_vectorPolarizationFactor
    (e : Fin 4 → ℝ) (n : ℕ) (α : Fin n → Fin 4) :
    (∑ β : Fin n → Fin 4,
      (∏ i : Fin n, stdStarStructure.C (α i) (β i)) *
        vectorPolarizationFactor e n (β ∘ Fin.rev)) =
      star (vectorPolarizationFactor e n α) := by
  rw [sum_prod_stdStarStructure_C_mul, vectorPolarizationFactor_comp_rev,
      star_vectorPolarizationFactor]

lemma vectorPolarizationFactor_eq_one_pow_mul_rev (e : Fin 4 → ℝ)
    (n : ℕ) (α : Fin n → Fin 4) :
    vectorPolarizationFactor e n α =
      (1 : ℂ) ^ (n * (n - 1) / 2) * vectorPolarizationFactor e n (α ∘ Fin.rev) := by
  rw [one_pow, one_mul, vectorPolarizationFactor_comp_rev]

lemma stdRep_sigma_pt :
    stdRep.σ (-1, 1) = (-1 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  change spinorPT.val.val = (-1 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)
  rw [spinorPT_val, neg_one_smul]

noncomputable def vectorMomentumW (e q : Fin 4 → ℝ) : WightmanFamily (Fin 4) :=
  coeffMomentumW (vectorPolarizationFactor e) q

noncomputable def vectorMomentumH (e q : Fin 4 → ℝ) :
    ∀ n : ℕ, (Fin n → Fin 4) → (Fin n → Fin 4 → ℂ) → ℂ :=
  coeffMomentumH (vectorPolarizationFactor e) q

noncomputable def vectorMomentumTubeExtension (e q : Fin 4 → ℝ) :
    TubeExtension (vectorMomentumW e q) :=
  coeffMomentumTubeExtension (vectorPolarizationFactor e) q

noncomputable def vectorMomentumS (e q : Fin 4 → ℝ) : SchwingerFamily (Fin 4) :=
  coeffMomentumS (vectorPolarizationFactor e) q

@[simp]
lemma vectorMomentumTubeExtension_H (e q : Fin 4 → ℝ) :
    (vectorMomentumTubeExtension e q).H = vectorMomentumH e q := rfl

@[simp]
lemma vectorMomentumW_apply (e q : Fin 4 → ℝ) (n : ℕ) (α : Fin n → Fin 4)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    vectorMomentumW e q n α f =
      vectorPolarizationFactor e n α * fourMomentumW q n default f :=
  coeffMomentumW_apply (vectorPolarizationFactor e) q n α f

@[simp]
lemma vectorMomentumH_apply (e q : Fin 4 → ℝ) (n : ℕ) (α : Fin n → Fin 4)
    (z : Fin n → Fin 4 → ℂ) :
    vectorMomentumH e q n α z =
      vectorPolarizationFactor e n α * fourMomentumH q n default z := rfl

@[simp]
lemma vectorMomentumS_apply (e q : Fin 4 → ℝ) (n : ℕ) (α : Fin n → Fin 4)
    (x : Fin n → Fin 4 → ℝ) :
    vectorMomentumS e q n α x =
      vectorPolarizationFactor e n α * fourMomentumS q n default x := rfl

@[simp]
theorem vectorMomentumH_two_euclidTimeVec (e : Fin 4 → ℝ) (E : ℝ)
    (α : Fin 2 → Fin 4) (z : Fin 2 → Fin 4 → ℂ) :
    vectorMomentumH e (euclidTimeVec E) 2 α z =
      ((e (α 0) : ℂ) * (e (α 1) : ℂ)) * spectralTwoPointTube E z := by
  rw [vectorMomentumH_apply, vectorPolarizationFactor_two, fourMomentumH_two_euclidTimeVec]

@[simp]
theorem vectorMomentumS_two_euclidTimeVec (e : Fin 4 → ℝ) (E : ℝ)
    (α : Fin 2 → Fin 4) (x : Fin 2 → Fin 4 → ℝ) :
    vectorMomentumS e (euclidTimeVec E) 2 α x =
      ((e (α 0) : ℂ) * (e (α 1) : ℂ)) * euclidSpectralTwoPoint E x := by
  rw [vectorMomentumS_apply, vectorPolarizationFactor_two, fourMomentumS_two_euclidTimeVec]

theorem vectorMomentumS_two_base_ne_doubleBase {e q : Fin 4 → ℝ}
    {μ ν : Fin 4} (hμ : e μ ≠ 0) (hν : e ν ≠ 0) (hq0 : q 0 ≠ 0) :
    vectorMomentumS e q 2 ![μ, ν] (euclidOrderedBasePoint 2) ≠
      vectorMomentumS e q 2 ![μ, ν] euclidTwoPointDoubleBase := by
  rw [vectorMomentumS_apply, vectorMomentumS_apply, vectorPolarizationFactor_two]
  have h_coeff : (e (![μ, ν] 0) : ℂ) * (e (![μ, ν] 1) : ℂ) ≠ 0 := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hμ) (Complex.ofReal_ne_zero.mpr hν)
  intro h_eq
  exact fourMomentumS_two_base_ne_doubleBase hq0 default (mul_left_cancel₀ h_coeff h_eq)

theorem vectorMomentumTubeTranslationInvariant (e q : Fin 4 → ℝ) :
    TubeTranslationInvariant (vectorMomentumTubeExtension e q) :=
  coeffMomentumTubeTranslationInvariant (vectorPolarizationFactor e) q

theorem vectorMomentumOSTranslationInvariant (e q : Fin 4 → ℝ) :
    OSTranslationInvariant (vectorMomentumS e q) :=
  coeffMomentumOSTranslationInvariant (vectorPolarizationFactor e) q

theorem vectorMomentumW_translationInvariant (e q : Fin 4 → ℝ)
    (n : ℕ) (α : Fin n → Fin 4) (a : Fin 4 → ℝ)
    (f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hf' : ∀ x : Fin n → Fin 4 → ℝ, f' (fun i => x i + a) = f x) :
    vectorMomentumW e q n α f' = vectorMomentumW e q n α f :=
  coeffMomentumW_translationInvariant (vectorPolarizationFactor e) q n α a f f' hf'

theorem vectorMomentumTubeWickHermiticity (e q : Fin 4 → ℝ) :
    TubeWickHermiticity stdStarStructure (vectorMomentumTubeExtension e q) :=
  coeffMomentumTubeWickHermiticity stdStarStructure
    (sum_prod_stdStarStructure_C_mul_vectorPolarizationFactor e) q

theorem vectorMomentumOSHermiticity (e q : Fin 4 → ℝ) :
    OSHermiticity stdStarStructure (vectorMomentumS e q) :=
  coeffMomentumOSHermiticity stdStarStructure
    (sum_prod_stdStarStructure_C_mul_vectorPolarizationFactor e) q

theorem vectorMomentumTubeWeakLocality_one (e q : Fin 4 → ℝ) :
    TubeWeakLocality 1 (vectorMomentumTubeExtension e q) :=
  coeffMomentumTubeWeakLocality (vectorPolarizationFactor_eq_one_pow_mul_rev e) q

theorem vectorMomentumOSSymmetric (e q : Fin 4 → ℝ)
    (n : ℕ) (α : Fin n → Fin 4) (x : Fin n → Fin 4 → ℝ)
    (hx : x ∈ orderedEuclidN n) :
    vectorMomentumS e q n α (-(x ∘ Fin.rev)) =
      (1 : ℂ) ^ (n * (n - 1) / 2) * vectorMomentumS e q n (α ∘ Fin.rev) x :=
  coeffMomentumOSSymmetric (vectorPolarizationFactor_eq_one_pow_mul_rev e) q n α x hx

theorem vectorMomentumW_pct (e q : Fin 4 → ℝ) :
    WightmanPCT 1 stdRep (vectorMomentumW e q) :=
  coeffMomentumW_pct_of_sigma_pt_eq_neg_one stdRep stdRep_sigma_pt
    (vectorMomentumTubeWeakLocality_one e q)

theorem vectorMomentumW_forwardConeSpectrumCondition (e : Fin 4 → ℝ)
    {q : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone) :
    ForwardConeSpectrumCondition (vectorMomentumW e q) :=
  coeffMomentumW_forwardConeSpectrumCondition (vectorPolarizationFactor e) hq

theorem norm_vectorMomentumH_le (e : Fin 4 → ℝ) {q : Fin 4 → ℝ}
    (hq : q ∈ closure forward_light_cone) (n : ℕ) (α : Fin n → Fin 4)
    {z : Fin n → Fin 4 → ℂ} (hz : z ∈ forward_tube_n n) :
    ‖vectorMomentumH e q n α z‖ ≤ ‖vectorPolarizationFactor e n α‖ :=
  norm_coeffMomentumH_le (vectorPolarizationFactor e) hq n α hz

theorem osScalarRotInvariant_vectorMomentumS_euclidTimeVec (e : Fin 4 → ℝ) (E : ℝ) :
    OSScalarRotInvariant (vectorMomentumS e (euclidTimeVec E)) :=
  osScalarRotInvariant_coeffMomentumS_euclidTimeVec (vectorPolarizationFactor e) E

theorem vectorMomentumW_positivity (e q : Fin 4 → ℝ) :
    Positivity stdStarStructure (vectorMomentumW e q) := by
  intro N F G hG
  let A_even : ℕ → ℂ := fun j =>
    if j % 2 = 0 then
      ∑ α : Fin j → Fin 4,
        vectorPolarizationFactor e j α *
          minkowskiFourier (F j α) (alternatingMomentum j q)
    else 0
  let A_odd : ℕ → ℂ := fun j =>
    if j % 2 = 1 then
      ∑ α : Fin j → Fin 4,
        vectorPolarizationFactor e j α *
          minkowskiFourier (F j α) (-alternatingMomentum j q)
    else 0
  have h_pair : ∀ (j k : ℕ) (α : Fin j → Fin 4) (α' : Fin k → Fin 4),
      (∑ β : Fin j → Fin 4,
        (∏ i, stdStarStructure.C (α i) (β i)) *
          vectorMomentumW e q (j + k) (Fin.append (β ∘ Fin.rev) α') (G j k α α')) =
      (if j % 2 = 0 ∧ k % 2 = 0 then
        (starRingEnd ℂ) (vectorPolarizationFactor e j α *
          minkowskiFourier (F j α) (alternatingMomentum j q)) *
          (vectorPolarizationFactor e k α' *
            minkowskiFourier (F k α') (alternatingMomentum k q))
      else 0) +
      (if j % 2 = 1 ∧ k % 2 = 1 then
        (starRingEnd ℂ) (vectorPolarizationFactor e j α *
          minkowskiFourier (F j α) (-alternatingMomentum j q)) *
          (vectorPolarizationFactor e k α' *
            minkowskiFourier (F k α') (-alternatingMomentum k q))
      else 0) := by
    intro j k α α'
    rw [sum_prod_stdStarStructure_C_mul, vectorMomentumW_apply,
        vectorPolarizationFactor_append, vectorPolarizationFactor_comp_rev,
        fourMomentumW_apply_split_rev_mul q j k (F j α) (F k α')
          (G j k α α') (hG j k α α') default]
    have hstar : (starRingEnd ℂ) (vectorPolarizationFactor e j α) =
        vectorPolarizationFactor e j α := star_vectorPolarizationFactor e j α
    by_cases hj0 : j % 2 = 0 <;> by_cases hk0 : k % 2 = 0
    · simp only [hj0, hk0, and_self, ↓reduceIte, Nat.zero_ne_one, add_zero,
        map_mul, hstar]
      ring
    · simp [hj0, hk0]
    · simp [hj0, hk0]
    · have hj1 : j % 2 = 1 := by omega
      have hk1 : k % 2 = 1 := by omega
      simp only [hj1, hk1, and_self, ↓reduceIte, one_ne_zero, zero_add,
        map_mul, hstar]
      ring
  have h_term : ∀ j k : ℕ,
      (∑ α : Fin j → Fin 4, ∑ α' : Fin k → Fin 4, ∑ β : Fin j → Fin 4,
        (∏ i, stdStarStructure.C (α i) (β i)) *
          vectorMomentumW e q (j + k) (Fin.append (β ∘ Fin.rev) α') (G j k α α')) =
      (starRingEnd ℂ) (A_even j) * A_even k +
        (starRingEnd ℂ) (A_odd j) * A_odd k := by
    intro j k
    simp_rw [h_pair j k, Finset.sum_add_distrib]
    dsimp [A_even, A_odd]
    by_cases hj0 : j % 2 = 0 <;> by_cases hk0 : k % 2 = 0
    · simp only [hj0, hk0, and_self, ↓reduceIte, Nat.zero_ne_one,
        Finset.sum_const_zero, map_zero, zero_mul, add_zero, map_sum,
        ← Finset.sum_mul, ← Finset.mul_sum]
    · simp [hj0, hk0]
    · simp [hj0, hk0]
    · have hj1 : j % 2 = 1 := by omega
      have hk1 : k % 2 = 1 := by omega
      simp only [hj1, hk1, and_self, ↓reduceIte, one_ne_zero,
        Finset.sum_const_zero, map_zero, zero_mul, zero_add, map_sum,
        ← Finset.sum_mul, ← Finset.mul_sum]
  simp_rw [h_term, Finset.sum_add_distrib,
      sum_star_mul_eq_normSq (Finset.range (N + 1)) A_even,
      sum_star_mul_eq_normSq (Finset.range (N + 1)) A_odd]
  have h_nonneg : 0 ≤
      Complex.normSq (∑ j ∈ Finset.range (N + 1), A_even j) +
        Complex.normSq (∑ j ∈ Finset.range (N + 1), A_odd j) :=
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  exact_mod_cast h_nonneg

def osConfigToUnit (A : OSConfig ι) : OSConfig Unit :=
  ⟨A.1, (default, A.2.2)⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma osConfigToUnit_fst (A : OSConfig ι) : (osConfigToUnit A).1 = A.1 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma osConfigToUnit_snd_snd (A : OSConfig ι) : (osConfigToUnit A).2.2 = A.2.2 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma osConfigToUnit_timeShift (τ : ℝ) (hτ : 0 ≤ τ) (A : OSConfig ι) :
    osConfigToUnit (osConfigTimeShift τ hτ A) =
      osConfigTimeShift τ hτ (osConfigToUnit A) := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma osConfigToUnit_osVacuumConfig :
    osConfigToUnit (osVacuumConfig ι) = osVacuumConfig Unit := rfl

@[simp]
lemma vectorPolarizationFactor_osConfigTimeShift (e : Fin 4 → ℝ)
    (τ : ℝ) (hτ : 0 ≤ τ) (A : OSConfig (Fin 4)) :
    vectorPolarizationFactor e (osConfigTimeShift τ hτ A).1
      (osConfigTimeShift τ hτ A).2.1 =
      vectorPolarizationFactor e A.1 A.2.1 := rfl

theorem osKernel_vectorMomentumS_eq (e q : Fin 4 → ℝ) (A B : OSConfig (Fin 4)) :
    osKernel stdStarStructure (vectorMomentumS e q) A B =
      star (vectorPolarizationFactor e A.1 A.2.1) *
        vectorPolarizationFactor e B.1 B.2.1 *
        osKernel trivialStarStructure (fourMomentumS q)
          (osConfigToUnit A) (osConfigToUnit B) := by
  unfold osKernel
  rw [sum_prod_stdStarStructure_C_mul A.1 A.2.1, Fintype.sum_unique]
  have h_triv :
      (∏ i : Fin (osConfigToUnit A).1,
        trivialStarStructure.C ((osConfigToUnit A).2.1 i) ((default : Fin A.1 → Unit) i)) =
        1 := Finset.prod_eq_one (fun _ _ => rfl)
  rw [h_triv, one_mul]
  change vectorPolarizationFactor e (A.1 + B.1) (osConcatIdx A.1 B.1 A.2.1 B.2.1) *
      fourMomentumS q (A.1 + B.1) default
        (osConcatPoint A.1 B.1 A.2.2.val B.2.2.val) =
    star (vectorPolarizationFactor e A.1 A.2.1) *
      vectorPolarizationFactor e B.1 B.2.1 *
      fourMomentumS q (A.1 + B.1)
        (osConcatIdx A.1 B.1 default (osConfigToUnit B).2.1)
        (osConcatPoint A.1 B.1 A.2.2.val B.2.2.val)
  have h_idx :
      osConcatIdx A.1 B.1 (default : Fin A.1 → Unit) (osConfigToUnit B).2.1 = default :=
    Subsingleton.elim _ _
  rw [h_idx, vectorPolarizationFactor_osConcatIdx, star_vectorPolarizationFactor, mul_assoc]

theorem vectorMomentumOSReflectionPositive (e q : Fin 4 → ℝ) :
    OSReflectionPositive stdStarStructure (vectorMomentumS e q) := by
  intro Ψ
  unfold osPreInner Finsupp.sum
  simp_rw [osKernel_vectorMomentumS_eq, osKernel_fourMomentumS_eq]
  let f_even : OSConfig (Fin 4) → ℂ := fun A =>
    Ψ A * vectorPolarizationFactor e A.1 A.2.1 *
      fourMomentumEvenConfigTerm q (osConfigToUnit A)
  let f_odd : OSConfig (Fin 4) → ℂ := fun A =>
    Ψ A * vectorPolarizationFactor e A.1 A.2.1 *
      fourMomentumOddConfigTerm q (osConfigToUnit A)
  have h_split : ∀ A B : OSConfig (Fin 4),
      star (Ψ A) * Ψ B *
        (star (vectorPolarizationFactor e A.1 A.2.1) *
          vectorPolarizationFactor e B.1 B.2.1 *
          (star (fourMomentumEvenConfigTerm q (osConfigToUnit A)) *
            fourMomentumEvenConfigTerm q (osConfigToUnit B) +
          star (fourMomentumOddConfigTerm q (osConfigToUnit A)) *
            fourMomentumOddConfigTerm q (osConfigToUnit B))) =
      (starRingEnd ℂ) (f_even A) * f_even B +
        (starRingEnd ℂ) (f_odd A) * f_odd B := by
    intro A B
    dsimp [f_even, f_odd]
    simp only [map_mul]
    ring
  simp_rw [h_split, Finset.sum_add_distrib,
      sum_star_mul_eq_normSq Ψ.support f_even,
      sum_star_mul_eq_normSq Ψ.support f_odd]
  have h_nonneg : 0 ≤
      Complex.normSq (∑ A ∈ Ψ.support, f_even A) +
        Complex.normSq (∑ A ∈ Ψ.support, f_odd A) :=
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  exact_mod_cast h_nonneg

noncomputable def vectorMomentumOSData (e q : Fin 4 → ℝ) :
    OSReflectionPositiveData stdRep stdStarStructure where
  𝒮 := vectorMomentumS e q
  hermiticity := vectorMomentumOSHermiticity e q
  positivity := vectorMomentumOSReflectionPositive e q

@[simp]
lemma vectorMomentumOSData_S (e q : Fin 4 → ℝ) :
    (vectorMomentumOSData e q).𝒮 = vectorMomentumS e q := rfl

theorem vectorMomentumOSDiagonalKernelBounded (e : Fin 4 → ℝ)
    {q : Fin 4 → ℝ} (hq0 : 0 ≤ q 0) :
    OSDiagonalKernelBounded stdStarStructure (vectorMomentumS e q) := by
  intro A
  rcases fourMomentumOSDiagonalKernelBounded hq0 (osConfigToUnit A) with ⟨C, hC⟩
  refine ⟨‖vectorPolarizationFactor e A.1 A.2.1‖ ^ 2 * C, fun τ hτ => ?_⟩
  rw [osKernel_vectorMomentumS_eq, vectorPolarizationFactor_osConfigTimeShift,
      star_vectorPolarizationFactor, osConfigToUnit_timeShift]
  rw [norm_mul, norm_mul, ← sq]
  exact mul_le_mul_of_nonneg_left (hC τ hτ) (sq_nonneg _)

theorem vectorMomentumOSContraction (e : Fin 4 → ℝ)
    {q : Fin 4 → ℝ} (hq0 : 0 ≤ q 0) :
    OSContractionCondition (vectorMomentumOSData e q) :=
  osContractionCondition_of_diagonalKernelBounded (vectorMomentumOSData e q)
    (vectorMomentumOSTranslationInvariant e q)
    (vectorMomentumOSDiagonalKernelBounded e hq0)

theorem vectorMomentumOSDiagonalKernelBounded_of_mem_closure_forward_light_cone
    (e : Fin 4 → ℝ) {q : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone) :
    OSDiagonalKernelBounded stdStarStructure (vectorMomentumS e q) :=
  vectorMomentumOSDiagonalKernelBounded e
    (zero_apply_nonneg_of_mem_closure_forward_light_cone hq)

theorem vectorMomentumOSContraction_of_mem_closure_forward_light_cone
    (e : Fin 4 → ℝ) {q : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone) :
    OSContractionCondition (vectorMomentumOSData e q) :=
  vectorMomentumOSContraction e
    (zero_apply_nonneg_of_mem_closure_forward_light_cone hq)

theorem vectorMomentumOSTimeCluster (e : Fin 4 → ℝ)
    {q : Fin 4 → ℝ} (hq0 : 0 < q 0) :
    OSTimeClusterDecomposition (vectorMomentumOSData e q) := by
  intro A B
  change Tendsto
    (fun τ : ℝ =>
      osKernel stdStarStructure (vectorMomentumS e q)
        A (osConfigTimeShift (max τ 0) (le_max_right τ 0) B))
    atTop
    (𝓝 (osKernel stdStarStructure (vectorMomentumS e q) A (osVacuumConfig (Fin 4)) *
      osKernel stdStarStructure (vectorMomentumS e q) (osVacuumConfig (Fin 4)) B))
  have h4 := fourMomentumOSTimeCluster hq0 (osConfigToUnit A) (osConfigToUnit B)
  change Tendsto
    (fun τ : ℝ =>
      osKernel trivialStarStructure (fourMomentumS q)
        (osConfigToUnit A)
        (osConfigTimeShift (max τ 0) (le_max_right τ 0) (osConfigToUnit B)))
    atTop
    (𝓝 (osKernel trivialStarStructure (fourMomentumS q)
          (osConfigToUnit A) (osVacuumConfig Unit) *
        osKernel trivialStarStructure (fourMomentumS q)
          (osVacuumConfig Unit) (osConfigToUnit B))) at h4
  have h_lim := h4.const_mul
    (star (vectorPolarizationFactor e A.1 A.2.1) *
      vectorPolarizationFactor e B.1 B.2.1)
  have h_vac : vectorPolarizationFactor e (osVacuumConfig (Fin 4)).1
      (osVacuumConfig (Fin 4)).2.1 = 1 :=
    vectorPolarizationFactor_zero e (osVacuumConfig (Fin 4)).2.1
  have h_target :
      (star (vectorPolarizationFactor e A.1 A.2.1) *
        vectorPolarizationFactor e B.1 B.2.1) *
        (osKernel trivialStarStructure (fourMomentumS q)
          (osConfigToUnit A) (osVacuumConfig Unit) *
        osKernel trivialStarStructure (fourMomentumS q)
          (osVacuumConfig Unit) (osConfigToUnit B)) =
      osKernel stdStarStructure (vectorMomentumS e q) A (osVacuumConfig (Fin 4)) *
        osKernel stdStarStructure (vectorMomentumS e q) (osVacuumConfig (Fin 4)) B := by
    rw [osKernel_vectorMomentumS_eq e q A (osVacuumConfig (Fin 4)),
        osKernel_vectorMomentumS_eq e q (osVacuumConfig (Fin 4)) B,
        osConfigToUnit_osVacuumConfig, h_vac, star_one, mul_one, one_mul]
    ring
  rw [h_target] at h_lim
  refine h_lim.congr (fun τ => ?_)
  rw [osKernel_vectorMomentumS_eq, vectorPolarizationFactor_osConfigTimeShift,
      osConfigToUnit_timeShift]

theorem vectorMomentumOSTimeCluster_of_mem_closure_forward_light_cone
    (e : Fin 4 → ℝ) {q : Fin 4 → ℝ}
    (hq : q ∈ closure forward_light_cone) (hne : q ≠ 0) :
    OSTimeClusterDecomposition (vectorMomentumOSData e q) :=
  vectorMomentumOSTimeCluster e
    (zero_apply_pos_of_mem_closure_forward_light_cone hq hne)

theorem vectorMomentum_master (e : Fin 4 → ℝ) {E : ℝ} (hE : 0 ≤ E) :
    (∀ (α : Fin 2 → Fin 4) (z : Fin 2 → Fin 4 → ℂ),
      vectorMomentumH e (euclidTimeVec E) 2 α z =
        ((e (α 0) : ℂ) * (e (α 1) : ℂ)) * spectralTwoPointTube E z) ∧
    (∀ (α : Fin 2 → Fin 4) (x : Fin 2 → Fin 4 → ℝ),
      vectorMomentumS e (euclidTimeVec E) 2 α x =
        ((e (α 0) : ℂ) * (e (α 1) : ℂ)) * euclidSpectralTwoPoint E x) ∧
    TubeTranslationInvariant (vectorMomentumTubeExtension e (euclidTimeVec E)) ∧
    OSTranslationInvariant (vectorMomentumS e (euclidTimeVec E)) ∧
    TubeWickHermiticity stdStarStructure
      (vectorMomentumTubeExtension e (euclidTimeVec E)) ∧
    OSHermiticity stdStarStructure (vectorMomentumS e (euclidTimeVec E)) ∧
    TubeWeakLocality 1 (vectorMomentumTubeExtension e (euclidTimeVec E)) ∧
    WightmanPCT 1 stdRep (vectorMomentumW e (euclidTimeVec E)) ∧
    ForwardConeSpectrumCondition (vectorMomentumW e (euclidTimeVec E)) ∧
    Positivity stdStarStructure (vectorMomentumW e (euclidTimeVec E)) ∧
    OSReflectionPositive stdStarStructure (vectorMomentumS e (euclidTimeVec E)) ∧
    OSScalarRotInvariant (vectorMomentumS e (euclidTimeVec E)) ∧
    OSDiagonalKernelBounded stdStarStructure (vectorMomentumS e (euclidTimeVec E)) ∧
    OSContractionCondition (vectorMomentumOSData e (euclidTimeVec E)) := by
  have hq : euclidTimeVec E ∈ closure forward_light_cone :=
    euclidTimeVec_mem_closure_forward_light_cone hE
  exact ⟨vectorMomentumH_two_euclidTimeVec e E,
    vectorMomentumS_two_euclidTimeVec e E,
    vectorMomentumTubeTranslationInvariant e (euclidTimeVec E),
    vectorMomentumOSTranslationInvariant e (euclidTimeVec E),
    vectorMomentumTubeWickHermiticity e (euclidTimeVec E),
    vectorMomentumOSHermiticity e (euclidTimeVec E),
    vectorMomentumTubeWeakLocality_one e (euclidTimeVec E),
    vectorMomentumW_pct e (euclidTimeVec E),
    vectorMomentumW_forwardConeSpectrumCondition e hq,
    vectorMomentumW_positivity e (euclidTimeVec E),
    vectorMomentumOSReflectionPositive e (euclidTimeVec E),
    osScalarRotInvariant_vectorMomentumS_euclidTimeVec e E,
    vectorMomentumOSDiagonalKernelBounded_of_mem_closure_forward_light_cone e hq,
    vectorMomentumOSContraction_of_mem_closure_forward_light_cone e hq⟩

abbrev CompactSchwartz (n : ℕ) : Type _ :=
  { f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ //
    HasCompactSupport (f : (Fin n → Fin 4 → ℝ) → ℂ) }

def jostCompactSchwartz (n : ℕ) : CompactSchwartz n :=
  ⟨jostSchwartz n, jostBump_complex_hasCompactSupport n⟩

@[simp]
lemma jostCompactSchwartz_val (n : ℕ) :
    (jostCompactSchwartz n).val = jostSchwartz n := rfl

noncomputable def momentumWavepacketFun (n : ℕ) (p : Fin n → Fin 4 → ℝ)
    (x : Fin n → Fin 4 → ℝ) : ℂ :=
  (∫ y : Fin n → Fin 4 → ℝ, jostSchwartz n y)⁻¹ *
    (jostSchwartz n x *
      Complex.exp (Complex.I * ((∑ k : Fin n, minkowskiInner (p k) (x k) : ℝ) : ℂ)))

lemma momentumWavepacketFun_contDiff (n : ℕ) (p : Fin n → Fin 4 → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (momentumWavepacketFun n p) := by
  have h_phase : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Fin n → Fin 4 → ℝ =>
        Complex.exp (Complex.I * ((∑ k : Fin n, minkowskiInner (p k) (x k) : ℝ) : ℂ))) :=
    Complex.contDiff_exp.comp
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (minkowskiPhaseCLM n p).contDiff))
  exact contDiff_const.mul ((jostBump_complex_contDiff n).mul h_phase)

lemma momentumWavepacketFun_hasCompactSupport (n : ℕ) (p : Fin n → Fin 4 → ℝ) :
    HasCompactSupport (momentumWavepacketFun n p) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (jostBump_complex_hasCompactSupport n).isCompact (fun x hx => ?_)
  rw [Function.mem_support] at hx
  have h_jost : jostSchwartz n x ≠ 0 := by
    intro h0
    apply hx
    simp [momentumWavepacketFun, h0]
  exact subset_tsupport _ h_jost

noncomputable def momentumWavepacketSchwartz (n : ℕ) (p : Fin n → Fin 4 → ℝ) :
    SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
  (momentumWavepacketFun_hasCompactSupport n p).toSchwartzMap
    (momentumWavepacketFun_contDiff n p)

@[simp]
lemma momentumWavepacketSchwartz_apply (n : ℕ) (p : Fin n → Fin 4 → ℝ)
    (x : Fin n → Fin 4 → ℝ) :
    momentumWavepacketSchwartz n p x = momentumWavepacketFun n p x := rfl

noncomputable def momentumWavepacketCompactSchwartz (n : ℕ)
    (p : Fin n → Fin 4 → ℝ) : CompactSchwartz n :=
  ⟨momentumWavepacketSchwartz n p, momentumWavepacketFun_hasCompactSupport n p⟩

@[simp]
lemma momentumWavepacketCompactSchwartz_val (n : ℕ) (p : Fin n → Fin 4 → ℝ) :
    (momentumWavepacketCompactSchwartz n p).val = momentumWavepacketSchwartz n p := rfl

@[simp]
theorem minkowskiFourier_momentumWavepacketSchwartz_self (n : ℕ)
    (p : Fin n → Fin 4 → ℝ) :
    minkowskiFourier (momentumWavepacketSchwartz n p) p = 1 := by
  unfold minkowskiFourier
  have h_eq : (fun x : Fin n → Fin 4 → ℝ =>
      momentumWavepacketSchwartz n p x *
        Complex.exp (-(Complex.I * ((∑ k, minkowskiInner (p k) (x k) : ℝ) : ℂ)))) =
    fun x => (∫ y : Fin n → Fin 4 → ℝ, jostSchwartz n y)⁻¹ * jostSchwartz n x := by
    ext x
    change (∫ y : Fin n → Fin 4 → ℝ, jostSchwartz n y)⁻¹ *
        (jostSchwartz n x *
          Complex.exp (Complex.I * ((∑ k, minkowskiInner (p k) (x k) : ℝ) : ℂ))) *
        Complex.exp (-(Complex.I * ((∑ k, minkowskiInner (p k) (x k) : ℝ) : ℂ))) = _
    rw [mul_assoc, mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  rw [h_eq, MeasureTheory.integral_const_mul,
      inv_mul_cancel₀ (integral_jostSchwartz_ne_zero n)]

@[simp]
theorem integral_momentumWavepacketSchwartz_zero (n : ℕ) :
    (∫ x : Fin n → Fin 4 → ℝ, momentumWavepacketSchwartz n 0 x) = 1 := by
  rw [← minkowskiFourier_eval_zero_n]
  exact minkowskiFourier_momentumWavepacketSchwartz_self n 0

@[simp]
lemma momentumWavepacketSchwartz_zero_eval_zero :
    momentumWavepacketSchwartz 0 0 0 = 1 := by
  rw [← minkowskiFourier_fin0 (momentumWavepacketSchwartz 0 0) 0]
  exact minkowskiFourier_momentumWavepacketSchwartz_self 0 0

def wightmanConcatFun (j k : ℕ) (f : CompactSchwartz j) (g : CompactSchwartz k)
    (x : Fin (j + k) → Fin 4 → ℝ) : ℂ :=
  (starRingEnd ℂ) (f.val (fun i => x (Fin.castAdd k (Fin.rev i)))) *
    g.val (fun i => x (Fin.natAdd j i))

lemma wightmanConcatFun_contDiff (j k : ℕ)
    (f : CompactSchwartz j) (g : CompactSchwartz k) :
    ContDiff ℝ (⊤ : ℕ∞) (wightmanConcatFun j k f g) := by
  have h_left : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Fin (j + k) → Fin 4 → ℝ =>
        (fun i : Fin j => x (Fin.castAdd k (Fin.rev i)))) :=
    contDiff_pi.mpr (fun i => contDiff_apply ℝ (Fin 4 → ℝ) (Fin.castAdd k (Fin.rev i)))
  have h_right : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Fin (j + k) → Fin 4 → ℝ =>
        (fun i : Fin k => x (Fin.natAdd j i))) :=
    contDiff_pi.mpr (fun i => contDiff_apply ℝ (Fin 4 → ℝ) (Fin.natAdd j i))
  exact (Complex.conjCLE.contDiff.comp (f.val.smooth'.comp h_left)).mul
    (g.val.smooth'.comp h_right)

lemma wightmanConcatFun_hasCompactSupport (j k : ℕ)
    (f : CompactSchwartz j) (g : CompactSchwartz k) :
    HasCompactSupport (wightmanConcatFun j k f g) := by
  refine HasCompactSupport.of_support_subset_isCompact
    ((f.property.isCompact.prod g.property.isCompact).image
      (continuous_finAppendRevEquiv j k)) ?_
  intro x hx
  rw [Function.mem_support] at hx
  have h_left_ne : f.val (fun i => x (Fin.castAdd k (Fin.rev i))) ≠ 0 := by
    intro h0
    apply hx
    simp [wightmanConcatFun, h0]
  have h_right_ne : g.val (fun i => x (Fin.natAdd j i)) ≠ 0 := by
    intro h0
    apply hx
    simp [wightmanConcatFun, h0]
  refine ⟨((fun i => x (Fin.castAdd k (Fin.rev i))), (fun i => x (Fin.natAdd j i))),
    ⟨subset_tsupport _ h_left_ne, subset_tsupport _ h_right_ne⟩, ?_⟩
  exact (finAppendRevEquiv j k).toEquiv.right_inv x

noncomputable def wightmanConcatSchwartz (j k : ℕ)
    (f : CompactSchwartz j) (g : CompactSchwartz k) :
    SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ :=
  (wightmanConcatFun_hasCompactSupport j k f g).toSchwartzMap
    (wightmanConcatFun_contDiff j k f g)

@[simp]
lemma wightmanConcatSchwartz_apply (j k : ℕ)
    (f : CompactSchwartz j) (g : CompactSchwartz k)
    (x : Fin (j + k) → Fin 4 → ℝ) :
    wightmanConcatSchwartz j k f g x =
      (starRingEnd ℂ) (f.val (fun i => x (Fin.castAdd k (Fin.rev i)))) *
        g.val (fun i => x (Fin.natAdd j i)) := rfl

lemma integral_wightmanConcatSchwartz (j k : ℕ)
    (f : CompactSchwartz j) (g : CompactSchwartz k) :
    (∫ x : Fin (j + k) → Fin 4 → ℝ, wightmanConcatSchwartz j k f g x) =
      star (∫ y : Fin j → Fin 4 → ℝ, f.val y) *
        (∫ z : Fin k → Fin 4 → ℝ, g.val z) := by
  have h_eq : (fun x : Fin (j + k) → Fin 4 → ℝ => wightmanConcatSchwartz j k f g x) =
      fun x => ((fun y => (starRingEnd ℂ) (f.val y))
        (fun i => x (Fin.castAdd k (Fin.rev i)))) *
        ((fun z => g.val z) (fun i => x (Fin.natAdd j i))) := rfl
  rw [h_eq, integral_split_rev_mul j k
      (fun y => (starRingEnd ℂ) (f.val y)) (fun z => g.val z),
      integral_conj, ← Complex.star_def]

abbrev WightmanConfig (ι : Type*) : Type _ :=
  Σ n : ℕ, (Fin n → ι) × CompactSchwartz n

noncomputable def wightmanBaseConfig (n : ℕ) (α : Fin n → ι) : WightmanConfig ι :=
  ⟨n, (α, momentumWavepacketCompactSchwartz n 0)⟩

noncomputable def wightmanMomentumConfig (n : ℕ) (α : Fin n → ι)
    (p : Fin n → Fin 4 → ℝ) : WightmanConfig ι :=
  ⟨n, (α, momentumWavepacketCompactSchwartz n p)⟩

noncomputable def wightmanVacuumConfig (ι : Type*) : WightmanConfig ι :=
  wightmanBaseConfig 0 Fin.elim0

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanBaseConfig_fst (n : ℕ) (α : Fin n → ι) :
    (wightmanBaseConfig n α).1 = n := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanBaseConfig_snd_fst (n : ℕ) (α : Fin n → ι) :
    (wightmanBaseConfig n α).2.1 = α := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanBaseConfig_snd_snd (n : ℕ) (α : Fin n → ι) :
    (wightmanBaseConfig n α).2.2 = momentumWavepacketCompactSchwartz n 0 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanVacuumConfig_fst :
    (wightmanVacuumConfig ι).1 = 0 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanVacuumConfig_snd_snd :
    (wightmanVacuumConfig ι).2.2 = momentumWavepacketCompactSchwartz 0 0 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma integral_wightmanBaseConfig (n : ℕ) (α : Fin n → ι) :
    (∫ y : Fin (wightmanBaseConfig n α).1 → Fin 4 → ℝ,
      (wightmanBaseConfig n α).2.2.val y) = 1 :=
  integral_momentumWavepacketSchwartz_zero n

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma integral_wightmanVacuumConfig :
    (∫ y : Fin (wightmanVacuumConfig ι).1 → Fin 4 → ℝ,
      (wightmanVacuumConfig ι).2.2.val y) = 1 :=
  integral_momentumWavepacketSchwartz_zero 0

noncomputable def wightmanKernel {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) (A B : WightmanConfig ι) : ℂ :=
  ∑ β : Fin A.1 → ι,
    (∏ i : Fin A.1, S.C (A.2.1 i) (β i)) *
      W (A.1 + B.1) (osConcatIdx A.1 B.1 β B.2.1)
        (wightmanConcatSchwartz A.1 B.1 A.2.2 B.2.2)

noncomputable def wightmanPreInner {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) (Ψ Φ : WightmanConfig ι →₀ ℂ) : ℂ :=
  Ψ.sum fun A cA => Φ.sum fun B cB => star cA * cB * wightmanKernel S W A B

def WightmanKernelHermiticity {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) : Prop :=
  ∀ A B : WightmanConfig ι, star (wightmanKernel S W B A) = wightmanKernel S W A B

def WightmanKernelPositive {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) : Prop :=
  ∀ Ψ : WightmanConfig ι →₀ ℂ, 0 ≤ (wightmanPreInner S W Ψ Ψ).re

structure WightmanPositiveData (R : HolomorphicLorentzRep ι) (S : StarStructure R) where
  W : WightmanFamily ι
  hermiticity : WightmanKernelHermiticity S W
  positivity : WightmanKernelPositive S W

lemma wightmanPreInner_conj_symm {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Ψ Φ : WightmanConfig ι →₀ ℂ) :
    star (wightmanPreInner S WData.W Φ Ψ) = wightmanPreInner S WData.W Ψ Φ := by
  unfold wightmanPreInner
  rw [Finsupp.sum_comm]
  rw [star_finsuppSum]
  refine Finsupp.sum_congr (fun A _ => ?_)
  change star (Φ.sum fun B cB => star cB * Ψ A * wightmanKernel S WData.W B A) =
    Φ.sum fun B cB => star (Ψ A) * cB * wightmanKernel S WData.W A B
  rw [star_finsuppSum]
  refine Finsupp.sum_congr (fun B _ => ?_)
  change star (star (Φ B) * Ψ A * wightmanKernel S WData.W B A) =
    star (Ψ A) * Φ B * wightmanKernel S WData.W A B
  rw [star_mul', star_mul', star_star, WData.hermiticity A B]
  ring

lemma wightmanPreInner_add_left {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Ψ₁ Ψ₂ Φ : WightmanConfig ι →₀ ℂ) :
    wightmanPreInner S WData.W (Ψ₁ + Ψ₂) Φ =
      wightmanPreInner S WData.W Ψ₁ Φ + wightmanPreInner S WData.W Ψ₂ Φ := by
  unfold wightmanPreInner
  rw [Finsupp.sum_add_index']
  · intro A
    simp
  · intro A c₁ c₂
    simp [add_mul, Finsupp.sum_add]

lemma wightmanPreInner_smul_left {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Ψ Φ : WightmanConfig ι →₀ ℂ) (c : ℂ) :
    wightmanPreInner S WData.W (c • Ψ) Φ =
      star c * wightmanPreInner S WData.W Ψ Φ := by
  unfold wightmanPreInner
  rw [Finsupp.sum_smul_index]
  · rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr (fun A _ => ?_)
    rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr (fun B _ => ?_)
    rw [star_mul']
    ring
  · intro A
    simp

@[ext]
structure WightmanPreHilbertSpace {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) where
  ofFinsupp ::
  toFinsupp : WightmanConfig ι →₀ ℂ

namespace WightmanPreHilbertSpace

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  (WData : WightmanPositiveData R S)

instance : Zero (WightmanPreHilbertSpace WData) := ⟨⟨0⟩⟩
instance : Add (WightmanPreHilbertSpace WData) := ⟨fun x y => ⟨x.1 + y.1⟩⟩
instance : Neg (WightmanPreHilbertSpace WData) := ⟨fun x => ⟨-x.1⟩⟩
instance : Sub (WightmanPreHilbertSpace WData) := ⟨fun x y => ⟨x.1 - y.1⟩⟩
instance {M : Type*} [SMul M (WightmanConfig ι →₀ ℂ)] :
    SMul M (WightmanPreHilbertSpace WData) :=
  ⟨fun c x => ⟨c • x.1⟩⟩

@[simp] lemma toFinsupp_zero : (0 : WightmanPreHilbertSpace WData).toFinsupp = 0 := rfl
@[simp] lemma toFinsupp_add (x y : WightmanPreHilbertSpace WData) :
    (x + y).toFinsupp = x.toFinsupp + y.toFinsupp := rfl
@[simp] lemma toFinsupp_neg (x : WightmanPreHilbertSpace WData) :
    (-x).toFinsupp = -x.toFinsupp := rfl
@[simp] lemma toFinsupp_sub (x y : WightmanPreHilbertSpace WData) :
    (x - y).toFinsupp = x.toFinsupp - y.toFinsupp := rfl
@[simp] lemma toFinsupp_smul {M : Type*} [SMul M (WightmanConfig ι →₀ ℂ)]
    (c : M) (x : WightmanPreHilbertSpace WData) :
    (c • x).toFinsupp = c • x.toFinsupp := rfl

instance : AddCommGroup (WightmanPreHilbertSpace WData) :=
  Function.Injective.addCommGroup toFinsupp (fun _ _ => WightmanPreHilbertSpace.ext)
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance : Module ℂ (WightmanPreHilbertSpace WData) :=
  Function.Injective.module ℂ ⟨⟨toFinsupp, rfl⟩, fun _ _ => rfl⟩
    (fun _ _ => WightmanPreHilbertSpace.ext) (fun _ _ => rfl)

def equivFinsupp : WightmanPreHilbertSpace WData ≃ₗ[ℂ] (WightmanConfig ι →₀ ℂ) where
  toFun := toFinsupp
  invFun := ofFinsupp
  left_inv x := by cases x; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable instance : PreInnerProductSpace.Core ℂ (WightmanPreHilbertSpace WData) where
  inner Ψ Φ := wightmanPreInner S WData.W Ψ.toFinsupp Φ.toFinsupp
  conj_inner_symm Ψ Φ := wightmanPreInner_conj_symm WData Ψ.toFinsupp Φ.toFinsupp
  re_inner_nonneg Ψ := WData.positivity Ψ.toFinsupp
  add_left Ψ₁ Ψ₂ Φ := wightmanPreInner_add_left WData Ψ₁.toFinsupp Ψ₂.toFinsupp Φ.toFinsupp
  smul_left Ψ Φ c := wightmanPreInner_smul_left WData Ψ.toFinsupp Φ.toFinsupp c

noncomputable instance : SeminormedAddCommGroup (WightmanPreHilbertSpace WData) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)

noncomputable instance : InnerProductSpace ℂ (WightmanPreHilbertSpace WData) :=
  InnerProductSpace.ofCore _

@[simp]
lemma inner_def (Ψ Φ : WightmanPreHilbertSpace WData) :
    ⟪Ψ, Φ⟫_ℂ = wightmanPreInner S WData.W Ψ.toFinsupp Φ.toFinsupp := rfl

end WightmanPreHilbertSpace

noncomputable def wightmanBasisPre {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A : WightmanConfig ι) :
    WightmanPreHilbertSpace WData :=
  ⟨Finsupp.single A 1⟩

noncomputable def wightmanVacuumPre {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) : WightmanPreHilbertSpace WData :=
  wightmanBasisPre WData (wightmanVacuumConfig ι)

@[simp]
lemma inner_wightmanBasisPre {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A B : WightmanConfig ι) :
    ⟪wightmanBasisPre WData A, wightmanBasisPre WData B⟫_ℂ =
      wightmanKernel S WData.W A B := by
  change wightmanPreInner S WData.W (Finsupp.single A 1) (Finsupp.single B 1) =
    wightmanKernel S WData.W A B
  unfold wightmanPreInner
  simp

theorem wightmanPreHilbert_cauchy_schwarz {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Ψ Φ : WightmanPreHilbertSpace WData) :
    ‖⟪Ψ, Φ⟫_ℂ‖ ≤ ‖Ψ‖ * ‖Φ‖ :=
  norm_inner_le_norm Ψ Φ

lemma wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Ψ : WightmanPreHilbertSpace WData) :
    Ψ = Ψ.toFinsupp.sum (fun A c => c • wightmanBasisPre WData A) := by
  apply WightmanPreHilbertSpace.ext
  have h_map : (Ψ.toFinsupp.sum (fun A c => c • wightmanBasisPre WData A)).toFinsupp =
      Ψ.toFinsupp.sum (fun A c => c • (wightmanBasisPre WData A).toFinsupp) :=
    map_finsuppSum (WightmanPreHilbertSpace.equivFinsupp WData).toLinearMap Ψ.toFinsupp
      (fun A c => c • wightmanBasisPre WData A)
  rw [h_map]
  have h_single : (fun (A : WightmanConfig ι) (c : ℂ) =>
      c • (wightmanBasisPre WData A).toFinsupp) =
      fun A c => Finsupp.single A c := by
    ext A c B
    simp [wightmanBasisPre]
  rw [h_single, Finsupp.sum_single]

abbrev WightmanHilbert {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) : Type _ :=
  UniformSpace.Completion (WightmanPreHilbertSpace WData)

noncomputable def toWightmanHilbert {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) :
    WightmanPreHilbertSpace WData →L[ℂ] WightmanHilbert WData :=
  UniformSpace.Completion.toComplL

@[simp]
lemma inner_toWightmanHilbert {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Ψ Φ : WightmanPreHilbertSpace WData) :
    ⟪toWightmanHilbert WData Ψ, toWightmanHilbert WData Φ⟫_ℂ = ⟪Ψ, Φ⟫_ℂ :=
  UniformSpace.Completion.inner_coe Ψ Φ

@[simp]
lemma norm_toWightmanHilbert {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Ψ : WightmanPreHilbertSpace WData) :
    ‖toWightmanHilbert WData Ψ‖ = ‖Ψ‖ :=
  UniformSpace.Completion.norm_coe Ψ

noncomputable def wightmanBasis {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A : WightmanConfig ι) : WightmanHilbert WData :=
  toWightmanHilbert WData (wightmanBasisPre WData A)

noncomputable def wightmanVacuum {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) : WightmanHilbert WData :=
  toWightmanHilbert WData (wightmanVacuumPre WData)

@[simp]
lemma inner_wightmanBasis {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A B : WightmanConfig ι) :
    ⟪wightmanBasis WData A, wightmanBasis WData B⟫_ℂ =
      wightmanKernel S WData.W A B := by
  dsimp [wightmanBasis]
  rw [inner_toWightmanHilbert, inner_wightmanBasisPre]

theorem wightmanHilbert_cauchy_schwarz {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Ψ Φ : WightmanHilbert WData) :
    ‖⟪Ψ, Φ⟫_ℂ‖ ≤ ‖Ψ‖ * ‖Φ‖ :=
  norm_inner_le_norm Ψ Φ

lemma completion_coe_eq_of_inner_eq {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℂ E] {x y : E}
    (hxy : ⟪x, y⟫_ℂ = ⟪x, x⟫_ℂ) (hyx : ⟪y, x⟫_ℂ = ⟪x, x⟫_ℂ)
    (hyy : ⟪y, y⟫_ℂ = ⟪x, x⟫_ℂ) :
    (UniformSpace.Completion.toComplL : E →L[ℂ] UniformSpace.Completion E) x =
      (UniformSpace.Completion.toComplL : E →L[ℂ] UniformSpace.Completion E) y := by
  have h_norm :
      ‖(UniformSpace.Completion.toComplL : E →L[ℂ] UniformSpace.Completion E) (x - y)‖ =
        ‖x - y‖ :=
    UniformSpace.Completion.norm_coe (x - y)
  rw [← sub_eq_zero, ← norm_eq_zero, ← map_sub, h_norm,
      norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_sub_left, inner_sub_right, inner_sub_right,
      hxy, hyx, hyy, sub_self, map_zero, Real.sqrt_zero]

theorem wightmanKernel_eq_vladimirovKernel_mul_integral
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {W : WightmanFamily ι} (hspec : ZeroMomentumSpectrumCondition W)
    (A B : WightmanConfig ι) :
    wightmanKernel S W A B =
      star (∫ y : Fin A.1 → Fin 4 → ℝ, A.2.2.val y) *
        (∫ z : Fin B.1 → Fin 4 → ℝ, B.2.2.val z) *
        vladimirovKernel S W A.1 B.1 A.2.1 B.2.1 := by
  rcases A with ⟨j, α, f⟩
  rcases B with ⟨k, α', g⟩
  unfold wightmanKernel vladimirovKernel osConcatIdx
  dsimp only
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  rw [W_n_eq_vladimirov_H_zero_mul_integral hspec (j + k)
      (Fin.append (β ∘ Fin.rev) α') (wightmanConcatSchwartz j k f g),
      integral_wightmanConcatSchwartz]
  ring

theorem wightmanKernel_eq_osKernel_mul_integral
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {𝒮 : SchwingerFamily ι} {W : WightmanFamily ι} (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = vladimirovSchwinger W n α x)
    (A B : WightmanConfig ι) :
    wightmanKernel S W A B =
      star (∫ y : Fin A.1 → Fin 4 → ℝ, A.2.2.val y) *
        (∫ z : Fin B.1 → Fin 4 → ℝ, B.2.2.val z) *
        osKernel S 𝒮 (osIndexedBaseConfig A.1 A.2.1) (osIndexedBaseConfig B.1 B.2.1) := by
  rw [wightmanKernel_eq_vladimirovKernel_mul_integral S hspec A B,
      osKernel_eq_vladimirovKernel_of_schwinger_eq S hspec h_schw]
  rfl

noncomputable def osConfigToWightmanConfig (A : OSConfig ι) : WightmanConfig ι :=
  wightmanBaseConfig A.1 A.2.1

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma osConfigToWightmanConfig_fst (A : OSConfig ι) :
    (osConfigToWightmanConfig A).1 = A.1 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma osConfigToWightmanConfig_snd_fst (A : OSConfig ι) :
    (osConfigToWightmanConfig A).2.1 = A.2.1 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma integral_osConfigToWightmanConfig (A : OSConfig ι) :
    (∫ y : Fin (osConfigToWightmanConfig A).1 → Fin 4 → ℝ,
      (osConfigToWightmanConfig A).2.2.val y) = 1 :=
  integral_momentumWavepacketSchwartz_zero A.1

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma osConfigToWightmanConfig_osVacuumConfig :
    osConfigToWightmanConfig (osVacuumConfig ι) = wightmanVacuumConfig ι := rfl

theorem wightmanKernel_osConfigToWightmanConfig_eq_osKernel
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {𝒮 : SchwingerFamily ι} {W : WightmanFamily ι} (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = vladimirovSchwinger W n α x)
    (A B : OSConfig ι) :
    wightmanKernel S W (osConfigToWightmanConfig A) (osConfigToWightmanConfig B) =
      osKernel S 𝒮 A B := by
  rw [wightmanKernel_eq_vladimirovKernel_mul_integral S hspec,
      osKernel_eq_vladimirovKernel_of_schwinger_eq S hspec h_schw,
      integral_osConfigToWightmanConfig, integral_osConfigToWightmanConfig,
      star_one, mul_one, one_mul]
  rfl

theorem wightmanKernelHermiticity_of_osData
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) {W : WightmanFamily ι}
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x) :
    WightmanKernelHermiticity S W := by
  intro A B
  rw [wightmanKernel_eq_osKernel_mul_integral S hspec h_schw B A,
      wightmanKernel_eq_osKernel_mul_integral S hspec h_schw A B,
      star_mul', star_mul', star_star,
      osKernel_conj_symm S D.𝒮 D.hermiticity
        (osIndexedBaseConfig A.1 A.2.1) (osIndexedBaseConfig B.1 B.2.1)]
  ring

noncomputable def wightmanToOSPreVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Ψ : WightmanConfig ι →₀ ℂ) :
    OSPreHilbertSpace D :=
  Ψ.sum fun A cA =>
    (cA * ∫ y : Fin A.1 → Fin 4 → ℝ, A.2.2.val y) •
      osBasisPre D (osIndexedBaseConfig A.1 A.2.1)

theorem inner_wightmanToOSPreVec_eq_wightmanPreInner
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) {W : WightmanFamily ι}
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (Ψ Φ : WightmanConfig ι →₀ ℂ) :
    ⟪wightmanToOSPreVec D Ψ, wightmanToOSPreVec D Φ⟫_ℂ =
      wightmanPreInner S W Ψ Φ := by
  unfold wightmanToOSPreVec wightmanPreInner Finsupp.sum
  rw [sum_inner]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  rw [inner_sum]
  refine Finset.sum_congr rfl (fun B _ => ?_)
  dsimp only
  rw [inner_smul_left, inner_smul_right, inner_osBasisPre,
      wightmanKernel_eq_osKernel_mul_integral S hspec h_schw A B,
      ← Complex.star_def, star_mul']
  ring

theorem wightmanKernelPositive_of_osData
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) {W : WightmanFamily ι}
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x) :
    WightmanKernelPositive S W := by
  intro Ψ
  rw [← inner_wightmanToOSPreVec_eq_wightmanPreInner D hspec h_schw Ψ Ψ]
  exact D.positivity (wightmanToOSPreVec D Ψ).toFinsupp

noncomputable def wightmanPositiveDataOfOSData
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x) :
    WightmanPositiveData R S where
  W := W
  hermiticity := wightmanKernelHermiticity_of_osData D hspec h_schw
  positivity := wightmanKernelPositive_of_osData D hspec h_schw

@[simp]
lemma wightmanPositiveDataOfOSData_W
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x) :
    (wightmanPositiveDataOfOSData D W hspec h_schw).W = W := rfl

noncomputable def osToWightmanPreLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x) :
    OSPreHilbertSpace D →ₗ[ℂ]
      WightmanPreHilbertSpace (wightmanPositiveDataOfOSData D W hspec h_schw) :=
  (Finsupp.lsum ℂ (fun A =>
    LinearMap.toSpanSingleton ℂ
      (WightmanPreHilbertSpace (wightmanPositiveDataOfOSData D W hspec h_schw))
      (wightmanBasisPre (wightmanPositiveDataOfOSData D W hspec h_schw)
        (osConfigToWightmanConfig A)))).comp
    (OSPreHilbertSpace.equivFinsupp D).toLinearMap

@[simp]
lemma osToWightmanPreLM_osBasisPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (A : OSConfig ι) :
    osToWightmanPreLM D W hspec h_schw (osBasisPre D A) =
      wightmanBasisPre (wightmanPositiveDataOfOSData D W hspec h_schw)
        (osConfigToWightmanConfig A) := by
  dsimp [osToWightmanPreLM, osBasisPre, OSPreHilbertSpace.equivFinsupp]
  simp

theorem inner_osToWightmanPreLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (Ψ Φ : OSPreHilbertSpace D) :
    ⟪osToWightmanPreLM D W hspec h_schw Ψ,
      osToWightmanPreLM D W hspec h_schw Φ⟫_ℂ = ⟪Ψ, Φ⟫_ℂ := by
  let L := osToWightmanPreLM D W hspec h_schw
  have hL : ∀ X : OSPreHilbertSpace D,
      L X = ∑ A ∈ X.toFinsupp.support, X.toFinsupp A • L (osBasisPre D A) := by
    intro X
    conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D X]
    rw [map_finsuppSum]
    unfold Finsupp.sum
    refine Finset.sum_congr rfl (fun A _ => L.map_smul _ _)
  have hX : ∀ X : OSPreHilbertSpace D,
      X = ∑ A ∈ X.toFinsupp.support, X.toFinsupp A • osBasisPre D A := by
    intro X
    conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D X]
    rfl
  rw [hL Ψ, hL Φ]
  conv_rhs => rw [hX Ψ, hX Φ]
  rw [sum_inner, sum_inner]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  rw [inner_smul_left, inner_smul_left, inner_sum, inner_sum]
  congr 1
  refine Finset.sum_congr rfl (fun B _ => ?_)
  rw [inner_smul_right, inner_smul_right, osToWightmanPreLM_osBasisPre,
      osToWightmanPreLM_osBasisPre, inner_wightmanBasisPre, inner_osBasisPre,
      wightmanPositiveDataOfOSData_W,
      wightmanKernel_osConfigToWightmanConfig_eq_osKernel S hspec h_schw A B]

theorem norm_osToWightmanPreLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (Ψ : OSPreHilbertSpace D) :
    ‖osToWightmanPreLM D W hspec h_schw Ψ‖ = ‖Ψ‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_osToWightmanPreLM D W hspec h_schw Ψ Ψ]

noncomputable def osToWightmanPreCLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x) :
    OSPreHilbertSpace D →L[ℂ]
      WightmanPreHilbertSpace (wightmanPositiveDataOfOSData D W hspec h_schw) :=
  (osToWightmanPreLM D W hspec h_schw).mkContinuous 1 (fun Ψ => by
    rw [one_mul, norm_osToWightmanPreLM D W hspec h_schw Ψ])

noncomputable def osToWightmanHilbertCLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x) :
    OSHilbert D →L[ℂ]
      WightmanHilbert (wightmanPositiveDataOfOSData D W hspec h_schw) :=
  (osToWightmanPreCLM D W hspec h_schw).completion

@[simp]
lemma osToWightmanHilbertCLM_toOSHilbert
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (Ψ : OSPreHilbertSpace D) :
    osToWightmanHilbertCLM D W hspec h_schw (toOSHilbert D Ψ) =
      toWightmanHilbert (wightmanPositiveDataOfOSData D W hspec h_schw)
        (osToWightmanPreLM D W hspec h_schw Ψ) :=
  ContinuousLinearMap.completion_apply_coe (osToWightmanPreCLM D W hspec h_schw) Ψ

@[simp]
lemma osToWightmanHilbertCLM_osBasis
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (A : OSConfig ι) :
    osToWightmanHilbertCLM D W hspec h_schw (osBasis D A) =
      wightmanBasis (wightmanPositiveDataOfOSData D W hspec h_schw)
        (osConfigToWightmanConfig A) := by
  dsimp [osBasis, wightmanBasis]
  rw [osToWightmanHilbertCLM_toOSHilbert, osToWightmanPreLM_osBasisPre]

@[simp]
lemma osToWightmanHilbertCLM_osVacuum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x) :
    osToWightmanHilbertCLM D W hspec h_schw (osVacuum D) =
      wightmanVacuum (wightmanPositiveDataOfOSData D W hspec h_schw) :=
  osToWightmanHilbertCLM_osBasis D W hspec h_schw (osVacuumConfig ι)

theorem inner_osToWightmanHilbertCLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (x y : OSHilbert D) :
    ⟪osToWightmanHilbertCLM D W hspec h_schw x,
      osToWightmanHilbertCLM D W hspec h_schw y⟫_ℂ = ⟪x, y⟫_ℂ := by
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ Φ =>
    change ⟪osToWightmanHilbertCLM D W hspec h_schw (toOSHilbert D Ψ),
        osToWightmanHilbertCLM D W hspec h_schw (toOSHilbert D Φ)⟫_ℂ =
      ⟪toOSHilbert D Ψ, toOSHilbert D Φ⟫_ℂ
    rw [osToWightmanHilbertCLM_toOSHilbert, osToWightmanHilbertCLM_toOSHilbert,
        inner_toWightmanHilbert, inner_toOSHilbert,
        inner_osToWightmanPreLM D W hspec h_schw Ψ Φ]

theorem norm_osToWightmanHilbertCLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (x : OSHilbert D) :
    ‖osToWightmanHilbertCLM D W hspec h_schw x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_osToWightmanHilbertCLM D W hspec h_schw x x]

noncomputable def wightmanToOSPreLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x) :
    WightmanPreHilbertSpace (wightmanPositiveDataOfOSData D W hspec h_schw) →ₗ[ℂ]
      OSPreHilbertSpace D :=
  (Finsupp.lsum ℂ (fun A =>
    LinearMap.toSpanSingleton ℂ (OSPreHilbertSpace D)
      ((∫ y : Fin A.1 → Fin 4 → ℝ, A.2.2.val y) •
        osBasisPre D (osIndexedBaseConfig A.1 A.2.1)))).comp
    (WightmanPreHilbertSpace.equivFinsupp
      (wightmanPositiveDataOfOSData D W hspec h_schw)).toLinearMap

@[simp]
lemma wightmanToOSPreLM_wightmanBasisPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (A : WightmanConfig ι) :
    wightmanToOSPreLM D W hspec h_schw
      (wightmanBasisPre (wightmanPositiveDataOfOSData D W hspec h_schw) A) =
      (∫ y : Fin A.1 → Fin 4 → ℝ, A.2.2.val y) •
        osBasisPre D (osIndexedBaseConfig A.1 A.2.1) := by
  dsimp [wightmanToOSPreLM, wightmanBasisPre, WightmanPreHilbertSpace.equivFinsupp]
  simp

theorem inner_wightmanToOSPreLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (Ψ Φ : WightmanPreHilbertSpace (wightmanPositiveDataOfOSData D W hspec h_schw)) :
    ⟪wightmanToOSPreLM D W hspec h_schw Ψ,
      wightmanToOSPreLM D W hspec h_schw Φ⟫_ℂ = ⟪Ψ, Φ⟫_ℂ := by
  let WData := wightmanPositiveDataOfOSData D W hspec h_schw
  let L := wightmanToOSPreLM D W hspec h_schw
  have hL : ∀ X : WightmanPreHilbertSpace WData,
      L X = ∑ A ∈ X.toFinsupp.support, X.toFinsupp A • L (wightmanBasisPre WData A) := by
    intro X
    conv_lhs => rw [wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData X]
    rw [map_finsuppSum]
    unfold Finsupp.sum
    refine Finset.sum_congr rfl (fun A _ => L.map_smul _ _)
  have hX : ∀ X : WightmanPreHilbertSpace WData,
      X = ∑ A ∈ X.toFinsupp.support, X.toFinsupp A • wightmanBasisPre WData A := by
    intro X
    conv_lhs => rw [wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData X]
    rfl
  rw [hL Ψ, hL Φ]
  conv_rhs => rw [hX Ψ, hX Φ]
  rw [sum_inner, sum_inner]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  rw [inner_smul_left, inner_smul_left, inner_sum, inner_sum]
  congr 1
  refine Finset.sum_congr rfl (fun B _ => ?_)
  rw [inner_smul_right, inner_smul_right, wightmanToOSPreLM_wightmanBasisPre,
      wightmanToOSPreLM_wightmanBasisPre, inner_smul_left, inner_smul_right,
      inner_osBasisPre, inner_wightmanBasisPre, wightmanPositiveDataOfOSData_W,
      wightmanKernel_eq_osKernel_mul_integral S hspec h_schw A B, ← Complex.star_def]
  ring

theorem norm_wightmanToOSPreLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (Ψ : WightmanPreHilbertSpace (wightmanPositiveDataOfOSData D W hspec h_schw)) :
    ‖wightmanToOSPreLM D W hspec h_schw Ψ‖ = ‖Ψ‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_wightmanToOSPreLM D W hspec h_schw Ψ Ψ]

noncomputable def wightmanToOSPreCLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x) :
    WightmanPreHilbertSpace (wightmanPositiveDataOfOSData D W hspec h_schw) →L[ℂ]
      OSPreHilbertSpace D :=
  (wightmanToOSPreLM D W hspec h_schw).mkContinuous 1 (fun Ψ => by
    rw [one_mul, norm_wightmanToOSPreLM D W hspec h_schw Ψ])

noncomputable def wightmanToOSHilbertCLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x) :
    WightmanHilbert (wightmanPositiveDataOfOSData D W hspec h_schw) →L[ℂ]
      OSHilbert D :=
  (wightmanToOSPreCLM D W hspec h_schw).completion

@[simp]
lemma wightmanToOSHilbertCLM_toWightmanHilbert
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (Ψ : WightmanPreHilbertSpace (wightmanPositiveDataOfOSData D W hspec h_schw)) :
    wightmanToOSHilbertCLM D W hspec h_schw
      (toWightmanHilbert (wightmanPositiveDataOfOSData D W hspec h_schw) Ψ) =
      toOSHilbert D (wightmanToOSPreLM D W hspec h_schw Ψ) :=
  ContinuousLinearMap.completion_apply_coe (wightmanToOSPreCLM D W hspec h_schw) Ψ

@[simp]
lemma wightmanToOSHilbertCLM_wightmanBasis
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (A : WightmanConfig ι) :
    wightmanToOSHilbertCLM D W hspec h_schw
      (wightmanBasis (wightmanPositiveDataOfOSData D W hspec h_schw) A) =
      (∫ y : Fin A.1 → Fin 4 → ℝ, A.2.2.val y) •
        osBasis D (osIndexedBaseConfig A.1 A.2.1) := by
  dsimp [wightmanBasis, osBasis]
  rw [wightmanToOSHilbertCLM_toWightmanHilbert, wightmanToOSPreLM_wightmanBasisPre,
      (toOSHilbert D).map_smul]

@[simp]
lemma wightmanToOSHilbertCLM_wightmanVacuum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x) :
    wightmanToOSHilbertCLM D W hspec h_schw
      (wightmanVacuum (wightmanPositiveDataOfOSData D W hspec h_schw)) =
      osVacuum D := by
  unfold wightmanVacuum wightmanVacuumPre
  rw [← wightmanBasis, wightmanToOSHilbertCLM_wightmanBasis,
      integral_wightmanVacuumConfig, one_smul]
  rfl

theorem osBasis_eq_osIndexedBaseConfig_of_vladimirov
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) {W : WightmanFamily ι}
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (A : OSConfig ι) :
    osBasis D A = osBasis D (osIndexedBaseConfig A.1 A.2.1) := by
  refine completion_coe_eq_of_inner_eq ?_ ?_ ?_
  · rw [inner_osBasisPre, inner_osBasisPre,
        osKernel_eq_vladimirovKernel_of_schwinger_eq S hspec h_schw,
        osKernel_eq_vladimirovKernel_of_schwinger_eq S hspec h_schw]
    rfl
  · rw [inner_osBasisPre, inner_osBasisPre,
        osKernel_eq_vladimirovKernel_of_schwinger_eq S hspec h_schw,
        osKernel_eq_vladimirovKernel_of_schwinger_eq S hspec h_schw]
    rfl
  · rw [inner_osBasisPre, inner_osBasisPre,
        osKernel_eq_vladimirovKernel_of_schwinger_eq S hspec h_schw,
        osKernel_eq_vladimirovKernel_of_schwinger_eq S hspec h_schw]
    rfl

theorem wightmanBasis_eq_integral_smul_wightmanBaseConfig
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (A : WightmanConfig ι) :
    wightmanBasis (wightmanPositiveDataOfOSData D W hspec h_schw) A =
      (∫ y : Fin A.1 → Fin 4 → ℝ, A.2.2.val y) •
        wightmanBasis (wightmanPositiveDataOfOSData D W hspec h_schw)
          (wightmanBaseConfig A.1 A.2.1) := by
  let WData := wightmanPositiveDataOfOSData D W hspec h_schw
  have h_eq :
      toWightmanHilbert WData (wightmanBasisPre WData A) =
        toWightmanHilbert WData
          ((∫ y : Fin A.1 → Fin 4 → ℝ, A.2.2.val y) •
            wightmanBasisPre WData (wightmanBaseConfig A.1 A.2.1)) := by
    refine completion_coe_eq_of_inner_eq ?_ ?_ ?_
    · rw [inner_smul_right, inner_wightmanBasisPre, inner_wightmanBasisPre,
          wightmanPositiveDataOfOSData_W,
          wightmanKernel_eq_vladimirovKernel_mul_integral S hspec A
            (wightmanBaseConfig A.1 A.2.1),
          wightmanKernel_eq_vladimirovKernel_mul_integral S hspec A A,
          integral_wightmanBaseConfig, mul_one]
      dsimp only [wightmanBaseConfig]
      ring
    · rw [inner_smul_left, inner_wightmanBasisPre, inner_wightmanBasisPre,
          wightmanPositiveDataOfOSData_W,
          wightmanKernel_eq_vladimirovKernel_mul_integral S hspec
            (wightmanBaseConfig A.1 A.2.1) A,
          wightmanKernel_eq_vladimirovKernel_mul_integral S hspec A A,
          ← Complex.star_def, integral_wightmanBaseConfig, star_one, one_mul]
      dsimp only [wightmanBaseConfig]
      ring
    · rw [inner_smul_left, inner_smul_right, inner_wightmanBasisPre, inner_wightmanBasisPre,
          wightmanPositiveDataOfOSData_W,
          wightmanKernel_eq_vladimirovKernel_mul_integral S hspec
            (wightmanBaseConfig A.1 A.2.1) (wightmanBaseConfig A.1 A.2.1),
          wightmanKernel_eq_vladimirovKernel_mul_integral S hspec A A,
          ← Complex.star_def, integral_wightmanBaseConfig, star_one, one_mul, one_mul]
      dsimp only [wightmanBaseConfig]
      ring
  dsimp [wightmanBasis]
  rw [h_eq, (toWightmanHilbert WData).map_smul]

theorem wightmanToOSHilbertCLM_osToWightmanHilbertCLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (x : OSHilbert D) :
    wightmanToOSHilbertCLM D W hspec h_schw
      (osToWightmanHilbertCLM D W hspec h_schw x) = x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change wightmanToOSHilbertCLM D W hspec h_schw
      (osToWightmanHilbertCLM D W hspec h_schw (toOSHilbert D Ψ)) = toOSHilbert D Ψ
    have h_expand : toOSHilbert D Ψ =
        ∑ A ∈ Ψ.toFinsupp.support, Ψ.toFinsupp A • osBasis D A := by
      conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D Ψ]
      rw [map_finsuppSum]
      unfold Finsupp.sum
      refine Finset.sum_congr rfl (fun A _ => (toOSHilbert D).map_smul _ _)
    rw [h_expand, map_sum, map_sum]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    rw [map_smul, map_smul, osToWightmanHilbertCLM_osBasis,
        wightmanToOSHilbertCLM_wightmanBasis,
        integral_osConfigToWightmanConfig, one_smul]
    dsimp only [osConfigToWightmanConfig, wightmanBaseConfig]
    rw [← osBasis_eq_osIndexedBaseConfig_of_vladimirov D hspec h_schw A]

theorem osToWightmanHilbertCLM_wightmanToOSHilbertCLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (y : WightmanHilbert (wightmanPositiveDataOfOSData D W hspec h_schw)) :
    osToWightmanHilbertCLM D W hspec h_schw
      (wightmanToOSHilbertCLM D W hspec h_schw y) = y := by
  let WData := wightmanPositiveDataOfOSData D W hspec h_schw
  induction y using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change osToWightmanHilbertCLM D W hspec h_schw
      (wightmanToOSHilbertCLM D W hspec h_schw (toWightmanHilbert WData Ψ)) =
        toWightmanHilbert WData Ψ
    have h_expand : toWightmanHilbert WData Ψ =
        ∑ A ∈ Ψ.toFinsupp.support, Ψ.toFinsupp A • wightmanBasis WData A := by
      conv_lhs => rw [wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData Ψ]
      rw [map_finsuppSum]
      unfold Finsupp.sum
      refine Finset.sum_congr rfl (fun A _ => (toWightmanHilbert WData).map_smul _ _)
    rw [h_expand, map_sum, map_sum]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    rw [map_smul, map_smul, wightmanToOSHilbertCLM_wightmanBasis, map_smul,
        osToWightmanHilbertCLM_osBasis]
    dsimp [osConfigToWightmanConfig, osIndexedBaseConfig]
    rw [← wightmanBasis_eq_integral_smul_wightmanBaseConfig D W hspec h_schw A]

noncomputable def vladimirovOSWightmanLinearIsometryEquiv
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x) :
    OSHilbert D ≃ₗᵢ[ℂ]
      WightmanHilbert (wightmanPositiveDataOfOSData D W hspec h_schw) where
  toFun := osToWightmanHilbertCLM D W hspec h_schw
  map_add' := (osToWightmanHilbertCLM D W hspec h_schw).map_add
  map_smul' := (osToWightmanHilbertCLM D W hspec h_schw).map_smul
  invFun := wightmanToOSHilbertCLM D W hspec h_schw
  left_inv := wightmanToOSHilbertCLM_osToWightmanHilbertCLM D W hspec h_schw
  right_inv := osToWightmanHilbertCLM_wightmanToOSHilbertCLM D W hspec h_schw
  norm_map' := norm_osToWightmanHilbertCLM D W hspec h_schw

@[simp]
theorem vladimirovOSWightmanLinearIsometryEquiv_osVacuum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x) :
    vladimirovOSWightmanLinearIsometryEquiv D W hspec h_schw (osVacuum D) =
      wightmanVacuum (wightmanPositiveDataOfOSData D W hspec h_schw) :=
  osToWightmanHilbertCLM_osVacuum D W hspec h_schw

@[simp]
theorem vladimirovOSWightmanLinearIsometryEquiv_symm_wightmanVacuum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x) :
    (vladimirovOSWightmanLinearIsometryEquiv D W hspec h_schw).symm
      (wightmanVacuum (wightmanPositiveDataOfOSData D W hspec h_schw)) =
      osVacuum D :=
  wightmanToOSHilbertCLM_wightmanVacuum D W hspec h_schw

noncomputable def vacWightmanData (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    WightmanPositiveData R S :=
  wightmanPositiveDataOfOSData (vacOSData R S) vacW vacZeroMomentumSpectrumCondition
    (fun n α x _ => by rw [vladimirovSchwinger_vacW]; rfl)

noncomputable def vacOSWightmanLinearIsometryEquiv
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    OSHilbert (vacOSData R S) ≃ₗᵢ[ℂ] WightmanHilbert (vacWightmanData R S) :=
  vladimirovOSWightmanLinearIsometryEquiv (vacOSData R S) vacW vacZeroMomentumSpectrumCondition
    (fun n α x _ => by rw [vladimirovSchwinger_vacW]; rfl)

@[simp]
theorem vacOSWightmanLinearIsometryEquiv_osVacuum
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    vacOSWightmanLinearIsometryEquiv R S (osVacuum (vacOSData R S)) =
      wightmanVacuum (vacWightmanData R S) :=
  vladimirovOSWightmanLinearIsometryEquiv_osVacuum (vacOSData R S) vacW
    vacZeroMomentumSpectrumCondition
    (fun n α x _ => by rw [vladimirovSchwinger_vacW]; rfl)

noncomputable def z2FreeWightmanData :
    WightmanPositiveData trivialRep trivialStarStructure :=
  wightmanPositiveDataOfOSData z2FreeOSData z2FreeW
    (momentZeroMomentumSpectrumCondition z2FreeCoeff)
    (fun n α x _ => by
      change z2FreeS n α x = vladimirovSchwinger (momentW z2FreeCoeff) n α x
      rw [vladimirovSchwinger_momentW]
      rfl)

noncomputable def z2FreeOSWightmanLinearIsometryEquiv :
    OSHilbert z2FreeOSData ≃ₗᵢ[ℂ] WightmanHilbert z2FreeWightmanData :=
  vladimirovOSWightmanLinearIsometryEquiv z2FreeOSData z2FreeW
    (momentZeroMomentumSpectrumCondition z2FreeCoeff)
    (fun n α x _ => by
      change z2FreeS n α x = vladimirovSchwinger (momentW z2FreeCoeff) n α x
      rw [vladimirovSchwinger_momentW]
      rfl)

noncomputable def fourMomentumEvenWightmanTerm (q : Fin 4 → ℝ)
    (A : WightmanConfig Unit) : ℂ :=
  if A.1 % 2 = 0 then
    minkowskiFourier A.2.2.val (alternatingMomentum A.1 q)
  else 0

noncomputable def fourMomentumOddWightmanTerm (q : Fin 4 → ℝ)
    (A : WightmanConfig Unit) : ℂ :=
  if A.1 % 2 = 1 then
    minkowskiFourier A.2.2.val (-alternatingMomentum A.1 q)
  else 0

theorem wightmanKernel_fourMomentumW_eq (q : Fin 4 → ℝ)
    (A B : WightmanConfig Unit) :
    wightmanKernel trivialStarStructure (fourMomentumW q) A B =
      star (fourMomentumEvenWightmanTerm q A) * fourMomentumEvenWightmanTerm q B +
        star (fourMomentumOddWightmanTerm q A) * fourMomentumOddWightmanTerm q B := by
  rcases A with ⟨j, α, f⟩
  rcases B with ⟨k, α', g⟩
  unfold wightmanKernel fourMomentumEvenWightmanTerm fourMomentumOddWightmanTerm
  simp only [Fintype.sum_unique, trivialStarStructure, Matrix.one_apply_eq,
    Finset.prod_const_one, one_mul]
  rw [fourMomentumW_apply_split_rev_mul q j k f.val g.val
      (wightmanConcatSchwartz j k f g) (fun _ => rfl)]
  by_cases hj0 : j % 2 = 0 <;> by_cases hk0 : k % 2 = 0
  · simp [hj0, hk0]
  · simp [hj0, hk0]
  · simp [hj0, hk0]
  · have hj1 : j % 2 = 1 := by omega
    have hk1 : k % 2 = 1 := by omega
    simp [hj1, hk1]

theorem fourMomentumWightmanHermiticity (q : Fin 4 → ℝ) :
    WightmanKernelHermiticity trivialStarStructure (fourMomentumW q) := by
  intro A B
  rw [wightmanKernel_fourMomentumW_eq, wightmanKernel_fourMomentumW_eq,
      star_add, star_mul', star_mul', star_star, star_star]
  ring

theorem fourMomentumWightmanPositive (q : Fin 4 → ℝ) :
    WightmanKernelPositive trivialStarStructure (fourMomentumW q) := by
  intro Ψ
  unfold wightmanPreInner Finsupp.sum
  simp_rw [wightmanKernel_fourMomentumW_eq]
  let f_even : WightmanConfig Unit → ℂ := fun A =>
    Ψ A * fourMomentumEvenWightmanTerm q A
  let f_odd : WightmanConfig Unit → ℂ := fun A =>
    Ψ A * fourMomentumOddWightmanTerm q A
  have h_split : ∀ A B : WightmanConfig Unit,
      star (Ψ A) * Ψ B *
        (star (fourMomentumEvenWightmanTerm q A) * fourMomentumEvenWightmanTerm q B +
          star (fourMomentumOddWightmanTerm q A) * fourMomentumOddWightmanTerm q B) =
      (starRingEnd ℂ) (f_even A) * f_even B +
        (starRingEnd ℂ) (f_odd A) * f_odd B := by
    intro A B
    dsimp [f_even, f_odd]
    simp only [map_mul]
    ring
  simp_rw [h_split, Finset.sum_add_distrib,
      sum_star_mul_eq_normSq Ψ.support f_even,
      sum_star_mul_eq_normSq Ψ.support f_odd]
  have h_nonneg : 0 ≤
      Complex.normSq (∑ A ∈ Ψ.support, f_even A) +
        Complex.normSq (∑ A ∈ Ψ.support, f_odd A) :=
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  exact_mod_cast h_nonneg

noncomputable def fourMomentumWightmanData (q : Fin 4 → ℝ) :
    WightmanPositiveData trivialRep trivialStarStructure where
  W := fourMomentumW q
  hermiticity := fourMomentumWightmanHermiticity q
  positivity := fourMomentumWightmanPositive q

@[simp]
lemma fourMomentumWightmanData_W (q : Fin 4 → ℝ) :
    (fourMomentumWightmanData q).W = fourMomentumW q := rfl

@[simp]
lemma fourMomentumEvenWightmanTerm_wightmanVacuumConfig (q : Fin 4 → ℝ) :
    fourMomentumEvenWightmanTerm q (wightmanVacuumConfig Unit) = 1 := by
  unfold fourMomentumEvenWightmanTerm wightmanVacuumConfig wightmanBaseConfig
  dsimp only [momentumWavepacketCompactSchwartz_val]
  rw [if_pos rfl, minkowskiFourier_fin0, momentumWavepacketSchwartz_zero_eval_zero]

@[simp]
lemma fourMomentumOddWightmanTerm_wightmanVacuumConfig (q : Fin 4 → ℝ) :
    fourMomentumOddWightmanTerm q (wightmanVacuumConfig Unit) = 0 := by
  unfold fourMomentumOddWightmanTerm wightmanVacuumConfig wightmanBaseConfig
  simp

noncomputable def fourMomentumWightmanOneParticleConfig (q : Fin 4 → ℝ) :
    WightmanConfig Unit :=
  wightmanMomentumConfig 1 default (-alternatingMomentum 1 q)

@[simp]
lemma fourMomentumEvenWightmanTerm_oneParticleConfig (q : Fin 4 → ℝ) :
    fourMomentumEvenWightmanTerm q (fourMomentumWightmanOneParticleConfig q) = 0 := by
  unfold fourMomentumEvenWightmanTerm fourMomentumWightmanOneParticleConfig
    wightmanMomentumConfig
  simp

@[simp]
lemma fourMomentumOddWightmanTerm_oneParticleConfig (q : Fin 4 → ℝ) :
    fourMomentumOddWightmanTerm q (fourMomentumWightmanOneParticleConfig q) = 1 := by
  unfold fourMomentumOddWightmanTerm fourMomentumWightmanOneParticleConfig
    wightmanMomentumConfig
  dsimp only [momentumWavepacketCompactSchwartz_val]
  rw [if_pos rfl, minkowskiFourier_momentumWavepacketSchwartz_self]

noncomputable def fourMomentumWightmanOneParticlePre (q : Fin 4 → ℝ) :
    WightmanPreHilbertSpace (fourMomentumWightmanData q) :=
  wightmanBasisPre (fourMomentumWightmanData q)
    (fourMomentumWightmanOneParticleConfig q)

noncomputable def fourMomentumWightmanOneParticle (q : Fin 4 → ℝ) :
    WightmanHilbert (fourMomentumWightmanData q) :=
  toWightmanHilbert (fourMomentumWightmanData q)
    (fourMomentumWightmanOneParticlePre q)

@[simp]
lemma inner_wightmanBasisPre_fourMomentumWightmanData (q : Fin 4 → ℝ)
    (A B : WightmanConfig Unit) :
    ⟪wightmanBasisPre (fourMomentumWightmanData q) A,
      wightmanBasisPre (fourMomentumWightmanData q) B⟫_ℂ =
      star (fourMomentumEvenWightmanTerm q A) * fourMomentumEvenWightmanTerm q B +
        star (fourMomentumOddWightmanTerm q A) * fourMomentumOddWightmanTerm q B := by
  rw [inner_wightmanBasisPre, fourMomentumWightmanData_W, wightmanKernel_fourMomentumW_eq]

@[simp]
lemma inner_wightmanVacuumPre_fourMomentumWightmanData_wightmanBasisPre
    (q : Fin 4 → ℝ) (A : WightmanConfig Unit) :
    ⟪wightmanVacuumPre (fourMomentumWightmanData q),
      wightmanBasisPre (fourMomentumWightmanData q) A⟫_ℂ =
      fourMomentumEvenWightmanTerm q A := by
  unfold wightmanVacuumPre
  rw [inner_wightmanBasisPre_fourMomentumWightmanData]
  simp

@[simp]
lemma inner_wightmanBasisPre_wightmanVacuumPre_fourMomentumWightmanData
    (q : Fin 4 → ℝ) (A : WightmanConfig Unit) :
    ⟪wightmanBasisPre (fourMomentumWightmanData q) A,
      wightmanVacuumPre (fourMomentumWightmanData q)⟫_ℂ =
      star (fourMomentumEvenWightmanTerm q A) := by
  unfold wightmanVacuumPre
  rw [inner_wightmanBasisPre_fourMomentumWightmanData]
  simp

@[simp]
lemma inner_wightmanVacuumPre_fourMomentumWightmanData_self (q : Fin 4 → ℝ) :
    ⟪wightmanVacuumPre (fourMomentumWightmanData q),
      wightmanVacuumPre (fourMomentumWightmanData q)⟫_ℂ = 1 := by
  change ⟪wightmanVacuumPre (fourMomentumWightmanData q),
    wightmanBasisPre (fourMomentumWightmanData q) (wightmanVacuumConfig Unit)⟫_ℂ = 1
  rw [inner_wightmanVacuumPre_fourMomentumWightmanData_wightmanBasisPre]
  simp

@[simp]
lemma inner_fourMomentumWightmanOneParticlePre_wightmanBasisPre
    (q : Fin 4 → ℝ) (A : WightmanConfig Unit) :
    ⟪fourMomentumWightmanOneParticlePre q,
      wightmanBasisPre (fourMomentumWightmanData q) A⟫_ℂ =
      fourMomentumOddWightmanTerm q A := by
  unfold fourMomentumWightmanOneParticlePre
  rw [inner_wightmanBasisPre_fourMomentumWightmanData]
  simp

@[simp]
lemma inner_wightmanBasisPre_fourMomentumWightmanOneParticlePre
    (q : Fin 4 → ℝ) (A : WightmanConfig Unit) :
    ⟪wightmanBasisPre (fourMomentumWightmanData q) A,
      fourMomentumWightmanOneParticlePre q⟫_ℂ =
      star (fourMomentumOddWightmanTerm q A) := by
  unfold fourMomentumWightmanOneParticlePre
  rw [inner_wightmanBasisPre_fourMomentumWightmanData]
  simp

@[simp]
lemma inner_wightmanVacuumPre_fourMomentumWightmanOneParticlePre (q : Fin 4 → ℝ) :
    ⟪wightmanVacuumPre (fourMomentumWightmanData q),
      fourMomentumWightmanOneParticlePre q⟫_ℂ = 0 := by
  unfold fourMomentumWightmanOneParticlePre
  rw [inner_wightmanVacuumPre_fourMomentumWightmanData_wightmanBasisPre]
  simp

@[simp]
lemma inner_fourMomentumWightmanOneParticlePre_wightmanVacuumPre (q : Fin 4 → ℝ) :
    ⟪fourMomentumWightmanOneParticlePre q,
      wightmanVacuumPre (fourMomentumWightmanData q)⟫_ℂ = 0 := by
  unfold wightmanVacuumPre
  rw [inner_fourMomentumWightmanOneParticlePre_wightmanBasisPre]
  simp

@[simp]
lemma inner_fourMomentumWightmanOneParticlePre_self (q : Fin 4 → ℝ) :
    ⟪fourMomentumWightmanOneParticlePre q,
      fourMomentumWightmanOneParticlePre q⟫_ℂ = 1 := by
  change ⟪fourMomentumWightmanOneParticlePre q,
    wightmanBasisPre (fourMomentumWightmanData q)
      (fourMomentumWightmanOneParticleConfig q)⟫_ℂ = 1
  rw [inner_fourMomentumWightmanOneParticlePre_wightmanBasisPre]
  simp

@[simp]
theorem inner_wightmanVacuum_fourMomentumWightmanData_self (q : Fin 4 → ℝ) :
    ⟪wightmanVacuum (fourMomentumWightmanData q),
      wightmanVacuum (fourMomentumWightmanData q)⟫_ℂ = 1 := by
  dsimp [wightmanVacuum]
  rw [inner_toWightmanHilbert, inner_wightmanVacuumPre_fourMomentumWightmanData_self]

@[simp]
theorem norm_wightmanVacuum_fourMomentumWightmanData (q : Fin 4 → ℝ) :
    ‖wightmanVacuum (fourMomentumWightmanData q)‖ = 1 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_wightmanVacuum_fourMomentumWightmanData_self]
  simp

@[simp]
theorem inner_wightmanVacuum_fourMomentumWightmanData_wightmanBasis
    (q : Fin 4 → ℝ) (A : WightmanConfig Unit) :
    ⟪wightmanVacuum (fourMomentumWightmanData q),
      wightmanBasis (fourMomentumWightmanData q) A⟫_ℂ =
      fourMomentumEvenWightmanTerm q A := by
  dsimp [wightmanVacuum, wightmanBasis]
  rw [inner_toWightmanHilbert, inner_wightmanVacuumPre_fourMomentumWightmanData_wightmanBasisPre]

@[simp]
theorem inner_fourMomentumWightmanOneParticle_wightmanBasis
    (q : Fin 4 → ℝ) (A : WightmanConfig Unit) :
    ⟪fourMomentumWightmanOneParticle q,
      wightmanBasis (fourMomentumWightmanData q) A⟫_ℂ =
      fourMomentumOddWightmanTerm q A := by
  dsimp [fourMomentumWightmanOneParticle, wightmanBasis]
  rw [inner_toWightmanHilbert, inner_fourMomentumWightmanOneParticlePre_wightmanBasisPre]

@[simp]
theorem inner_wightmanVacuum_fourMomentumWightmanOneParticle (q : Fin 4 → ℝ) :
    ⟪wightmanVacuum (fourMomentumWightmanData q),
      fourMomentumWightmanOneParticle q⟫_ℂ = 0 := by
  dsimp [wightmanVacuum, fourMomentumWightmanOneParticle]
  rw [inner_toWightmanHilbert, inner_wightmanVacuumPre_fourMomentumWightmanOneParticlePre]

@[simp]
theorem inner_fourMomentumWightmanOneParticle_wightmanVacuum (q : Fin 4 → ℝ) :
    ⟪fourMomentumWightmanOneParticle q,
      wightmanVacuum (fourMomentumWightmanData q)⟫_ℂ = 0 := by
  dsimp [wightmanVacuum, fourMomentumWightmanOneParticle]
  rw [inner_toWightmanHilbert, inner_fourMomentumWightmanOneParticlePre_wightmanVacuumPre]

@[simp]
theorem inner_fourMomentumWightmanOneParticle_self (q : Fin 4 → ℝ) :
    ⟪fourMomentumWightmanOneParticle q,
      fourMomentumWightmanOneParticle q⟫_ℂ = 1 := by
  dsimp [fourMomentumWightmanOneParticle]
  rw [inner_toWightmanHilbert, inner_fourMomentumWightmanOneParticlePre_self]

@[simp]
theorem norm_fourMomentumWightmanOneParticle (q : Fin 4 → ℝ) :
    ‖fourMomentumWightmanOneParticle q‖ = 1 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_fourMomentumWightmanOneParticle_self]
  simp

theorem wightmanBasis_fourMomentumWightmanData_eq (q : Fin 4 → ℝ)
    (A : WightmanConfig Unit) :
    wightmanBasis (fourMomentumWightmanData q) A =
      fourMomentumEvenWightmanTerm q A • wightmanVacuum (fourMomentumWightmanData q) +
        fourMomentumOddWightmanTerm q A • fourMomentumWightmanOneParticle q := by
  let WData := fourMomentumWightmanData q
  have h_eq : toWightmanHilbert WData (wightmanBasisPre WData A) =
      toWightmanHilbert WData
        (fourMomentumEvenWightmanTerm q A • wightmanVacuumPre WData +
          fourMomentumOddWightmanTerm q A • fourMomentumWightmanOneParticlePre q) := by
    refine completion_coe_eq_of_inner_eq ?_ ?_ ?_
    · rw [inner_add_right, inner_smul_right, inner_smul_right,
          inner_wightmanBasisPre_wightmanVacuumPre_fourMomentumWightmanData,
          inner_wightmanBasisPre_fourMomentumWightmanOneParticlePre,
          inner_wightmanBasisPre_fourMomentumWightmanData,
          mul_comm (fourMomentumEvenWightmanTerm q A),
          mul_comm (fourMomentumOddWightmanTerm q A)]
    · rw [inner_add_left, inner_smul_left, inner_smul_left,
          inner_wightmanVacuumPre_fourMomentumWightmanData_wightmanBasisPre,
          inner_fourMomentumWightmanOneParticlePre_wightmanBasisPre,
          inner_wightmanBasisPre_fourMomentumWightmanData, ← Complex.star_def]
    · rw [inner_add_left, inner_add_right, inner_add_right,
          inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
          inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
          inner_wightmanVacuumPre_fourMomentumWightmanData_self,
          inner_wightmanVacuumPre_fourMomentumWightmanOneParticlePre,
          inner_fourMomentumWightmanOneParticlePre_wightmanVacuumPre,
          inner_fourMomentumWightmanOneParticlePre_self,
          inner_wightmanBasisPre_fourMomentumWightmanData, ← Complex.star_def]
      simp only [mul_one, mul_zero, add_zero, zero_add]
  dsimp [wightmanBasis, wightmanVacuum, fourMomentumWightmanOneParticle] at h_eq ⊢
  rw [h_eq, map_add, (toWightmanHilbert WData).map_smul,
      (toWightmanHilbert WData).map_smul]

theorem fourMomentumWightmanHilbert_eq_vacuum_add_oneParticle (q : Fin 4 → ℝ)
    (Φ : WightmanHilbert (fourMomentumWightmanData q)) :
    Φ = ⟪wightmanVacuum (fourMomentumWightmanData q), Φ⟫_ℂ •
          wightmanVacuum (fourMomentumWightmanData q) +
        ⟪fourMomentumWightmanOneParticle q, Φ⟫_ℂ •
          fourMomentumWightmanOneParticle q := by
  have h_basis : ∀ A : WightmanConfig Unit,
      wightmanBasis (fourMomentumWightmanData q) A =
        ⟪wightmanVacuum (fourMomentumWightmanData q),
          wightmanBasis (fourMomentumWightmanData q) A⟫_ℂ •
          wightmanVacuum (fourMomentumWightmanData q) +
        ⟪fourMomentumWightmanOneParticle q,
          wightmanBasis (fourMomentumWightmanData q) A⟫_ℂ •
          fourMomentumWightmanOneParticle q := by
    intro A
    rw [inner_wightmanVacuum_fourMomentumWightmanData_wightmanBasis,
        inner_fourMomentumWightmanOneParticle_wightmanBasis]
    exact wightmanBasis_fourMomentumWightmanData_eq q A
  induction Φ using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    let WData := fourMomentumWightmanData q
    change toWightmanHilbert WData Ψ =
      ⟪wightmanVacuum WData, toWightmanHilbert WData Ψ⟫_ℂ • wightmanVacuum WData +
      ⟪fourMomentumWightmanOneParticle q, toWightmanHilbert WData Ψ⟫_ℂ •
        fourMomentumWightmanOneParticle q
    have h_expand : toWightmanHilbert WData Ψ =
        ∑ A ∈ Ψ.toFinsupp.support, Ψ.toFinsupp A • wightmanBasis WData A := by
      conv_lhs => rw [wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData Ψ]
      rw [map_finsuppSum]
      unfold Finsupp.sum
      refine Finset.sum_congr rfl (fun A _ => (toWightmanHilbert WData).map_smul _ _)
    rw [h_expand, inner_sum, inner_sum, Finset.sum_smul, Finset.sum_smul,
        ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    rw [inner_smul_right, inner_smul_right, mul_smul, mul_smul, ← smul_add, ← h_basis A]

@[simp]
lemma orthogonalTwoLinearIsometryEquiv_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e₀ e₁ : H)
    (h00 : ⟪e₀, e₀⟫_ℂ = 1) (h01 : ⟪e₀, e₁⟫_ℂ = 0)
    (h10 : ⟪e₁, e₀⟫_ℂ = 0) (h11 : ⟪e₁, e₁⟫_ℂ = 1)
    (hn0 : ‖e₀‖ = 1) (hn1 : ‖e₁‖ = 1)
    (h_span : ∀ Φ : H, Φ = ⟪e₀, Φ⟫_ℂ • e₀ + ⟪e₁, Φ⟫_ℂ • e₁) (Φ : H) :
    orthogonalTwoLinearIsometryEquiv e₀ e₁ h00 h01 h10 h11 hn0 hn1 h_span Φ =
      WithLp.toLp 2 ![⟪e₀, Φ⟫_ℂ, ⟪e₁, Φ⟫_ℂ] := rfl

@[simp]
lemma orthogonalTwoLinearIsometryEquiv_symm_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e₀ e₁ : H)
    (h00 : ⟪e₀, e₀⟫_ℂ = 1) (h01 : ⟪e₀, e₁⟫_ℂ = 0)
    (h10 : ⟪e₁, e₀⟫_ℂ = 0) (h11 : ⟪e₁, e₁⟫_ℂ = 1)
    (hn0 : ‖e₀‖ = 1) (hn1 : ‖e₁‖ = 1)
    (h_span : ∀ Φ : H, Φ = ⟪e₀, Φ⟫_ℂ • e₀ + ⟪e₁, Φ⟫_ℂ • e₁)
    (v : EuclideanSpace ℂ (Fin 2)) :
    (orthogonalTwoLinearIsometryEquiv e₀ e₁ h00 h01 h10 h11 hn0 hn1 h_span).symm v =
      v.ofLp 0 • e₀ + v.ofLp 1 • e₁ := rfl

noncomputable def fourMomentumWightmanHilbertLinearIsometryEquiv (q : Fin 4 → ℝ) :
    WightmanHilbert (fourMomentumWightmanData q) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  orthogonalTwoLinearIsometryEquiv
    (wightmanVacuum (fourMomentumWightmanData q))
    (fourMomentumWightmanOneParticle q)
    (inner_wightmanVacuum_fourMomentumWightmanData_self q)
    (inner_wightmanVacuum_fourMomentumWightmanOneParticle q)
    (inner_fourMomentumWightmanOneParticle_wightmanVacuum q)
    (inner_fourMomentumWightmanOneParticle_self q)
    (norm_wightmanVacuum_fourMomentumWightmanData q)
    (norm_fourMomentumWightmanOneParticle q)
    (fourMomentumWightmanHilbert_eq_vacuum_add_oneParticle q)

noncomputable def fourMomentumOSWightmanLinearIsometryEquiv (q : Fin 4 → ℝ) :
    OSHilbert (fourMomentumOSData q) ≃ₗᵢ[ℂ]
      WightmanHilbert (fourMomentumWightmanData q) :=
  (fourMomentumHilbertLinearIsometryEquiv q).trans
    (fourMomentumWightmanHilbertLinearIsometryEquiv q).symm

@[simp]
theorem fourMomentumOSWightmanLinearIsometryEquiv_osVacuum (q : Fin 4 → ℝ) :
    fourMomentumOSWightmanLinearIsometryEquiv q (osVacuum (fourMomentumOSData q)) =
      wightmanVacuum (fourMomentumWightmanData q) := by
  dsimp [fourMomentumOSWightmanLinearIsometryEquiv,
    fourMomentumHilbertLinearIsometryEquiv,
    fourMomentumWightmanHilbertLinearIsometryEquiv]
  simp

@[simp]
theorem fourMomentumOSWightmanLinearIsometryEquiv_oneParticle (q : Fin 4 → ℝ) :
    fourMomentumOSWightmanLinearIsometryEquiv q (fourMomentumOneParticle q) =
      fourMomentumWightmanOneParticle q := by
  dsimp [fourMomentumOSWightmanLinearIsometryEquiv,
    fourMomentumHilbertLinearIsometryEquiv,
    fourMomentumWightmanHilbertLinearIsometryEquiv]
  simp

@[simp]
theorem fourMomentumOSWightmanLinearIsometryEquiv_symm_wightmanVacuum (q : Fin 4 → ℝ) :
    (fourMomentumOSWightmanLinearIsometryEquiv q).symm
      (wightmanVacuum (fourMomentumWightmanData q)) =
      osVacuum (fourMomentumOSData q) := by
  dsimp [fourMomentumOSWightmanLinearIsometryEquiv,
    fourMomentumHilbertLinearIsometryEquiv,
    fourMomentumWightmanHilbertLinearIsometryEquiv]
  simp

@[simp]
theorem fourMomentumOSWightmanLinearIsometryEquiv_symm_oneParticle (q : Fin 4 → ℝ) :
    (fourMomentumOSWightmanLinearIsometryEquiv q).symm
      (fourMomentumWightmanOneParticle q) =
      fourMomentumOneParticle q := by
  dsimp [fourMomentumOSWightmanLinearIsometryEquiv,
    fourMomentumHilbertLinearIsometryEquiv,
    fourMomentumWightmanHilbertLinearIsometryEquiv]
  simp

theorem fourMomentumOSWightmanLinearIsometryEquiv_osBasis
    (q : Fin 4 → ℝ) (A : OSConfig Unit) :
    fourMomentumOSWightmanLinearIsometryEquiv q (osBasis (fourMomentumOSData q) A) =
      fourMomentumEvenConfigTerm q A • wightmanVacuum (fourMomentumWightmanData q) +
        fourMomentumOddConfigTerm q A • fourMomentumWightmanOneParticle q := by
  rw [osBasis_fourMomentumOSData_eq, map_add, map_smul, map_smul,
      fourMomentumOSWightmanLinearIsometryEquiv_osVacuum,
      fourMomentumOSWightmanLinearIsometryEquiv_oneParticle]

theorem fourMomentumOSWightmanLinearIsometryEquiv_symm_wightmanBasis
    (q : Fin 4 → ℝ) (A : WightmanConfig Unit) :
    (fourMomentumOSWightmanLinearIsometryEquiv q).symm
      (wightmanBasis (fourMomentumWightmanData q) A) =
      fourMomentumEvenWightmanTerm q A • osVacuum (fourMomentumOSData q) +
        fourMomentumOddWightmanTerm q A • fourMomentumOneParticle q := by
  rw [wightmanBasis_fourMomentumWightmanData_eq, map_add, map_smul, map_smul,
      fourMomentumOSWightmanLinearIsometryEquiv_symm_wightmanVacuum,
      fourMomentumOSWightmanLinearIsometryEquiv_symm_oneParticle]

theorem fourMomentumOSWightman_twoPointTubePropagator_bridge
    {q : Fin 4 → ℝ} (hq0 : 0 ≤ q 0)
    (htrans : OSTranslationInvariant (fourMomentumOSData q).𝒮)
    (α : Fin 2 → Unit) (z : Fin 2 → Fin 4 → ℂ) :
    (fourMomentumOSSpectralDecomposition hq0).twoPointTubePropagator htrans
      ((fourMomentumOSWightmanLinearIsometryEquiv q).symm
        (fourMomentumWightmanOneParticle q))
      ((fourMomentumOSWightmanLinearIsometryEquiv q).symm
        (fourMomentumWightmanOneParticle q))
      0 z =
      fourMomentumH (euclidTimeVec (q 0)) 2 α z := by
  rw [fourMomentumOSWightmanLinearIsometryEquiv_symm_oneParticle]
  exact fourMomentumOSSpectralDecomposition_twoPointTubePropagator_oneParticle_zero_eq_fourMomentumH
    hq0 htrans α z

theorem wightmanKernel_multiMomentumW_eq (m : ℕ) (w : Fin m → ℝ)
    (q : Fin m → Fin 4 → ℝ) (A B : WightmanConfig Unit) :
    wightmanKernel trivialStarStructure (multiMomentumW m w q) A B =
      ∑ r : Fin m, (w r : ℂ) *
        wightmanKernel trivialStarStructure (fourMomentumW (q r)) A B := by
  rcases A with ⟨j, α, f⟩
  rcases B with ⟨k, α', g⟩
  unfold wightmanKernel
  simp only [Fintype.sum_unique, trivialStarStructure, Matrix.one_apply_eq,
    Finset.prod_const_one, one_mul, multiMomentumW_apply]

theorem wightmanPreInner_multiMomentumW_eq (m : ℕ) (w : Fin m → ℝ)
    (q : Fin m → Fin 4 → ℝ) (Ψ Φ : WightmanConfig Unit →₀ ℂ) :
    wightmanPreInner trivialStarStructure (multiMomentumW m w q) Ψ Φ =
      ∑ r : Fin m, (w r : ℂ) *
        wightmanPreInner trivialStarStructure (fourMomentumW (q r)) Ψ Φ := by
  unfold wightmanPreInner Finsupp.sum
  simp_rw [wightmanKernel_multiMomentumW_eq, Finset.mul_sum]
  rw [sum_sum_sum_fin_comm]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  refine Finset.sum_congr rfl (fun A _ => Finset.sum_congr rfl (fun B _ => ?_))
  ring

theorem multiMomentumWightmanHermiticity (m : ℕ) (w : Fin m → ℝ)
    (q : Fin m → Fin 4 → ℝ) :
    WightmanKernelHermiticity trivialStarStructure (multiMomentumW m w q) := by
  intro A B
  rw [wightmanKernel_multiMomentumW_eq, wightmanKernel_multiMomentumW_eq, star_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [star_mul', Complex.star_def, Complex.conj_ofReal,
      ← Complex.star_def, fourMomentumWightmanHermiticity (q r) A B]

theorem multiMomentumWightmanPositive {m : ℕ} {w : Fin m → ℝ}
    (hw : ∀ r : Fin m, 0 ≤ w r) (q : Fin m → Fin 4 → ℝ) :
    WightmanKernelPositive trivialStarStructure (multiMomentumW m w q) := by
  intro Ψ
  rw [wightmanPreInner_multiMomentumW_eq, Complex.re_sum]
  refine Finset.sum_nonneg (fun r _ => ?_)
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (hw r) (fourMomentumWightmanPositive (q r) Ψ)

noncomputable def multiMomentumWightmanData {m : ℕ} {w : Fin m → ℝ}
    (hw : ∀ r : Fin m, 0 ≤ w r) (q : Fin m → Fin 4 → ℝ) :
    WightmanPositiveData trivialRep trivialStarStructure where
  W := multiMomentumW m w q
  hermiticity := multiMomentumWightmanHermiticity m w q
  positivity := multiMomentumWightmanPositive hw q

@[simp]
lemma multiMomentumWightmanData_W {m : ℕ} {w : Fin m → ℝ}
    (hw : ∀ r : Fin m, 0 ≤ w r) (q : Fin m → Fin 4 → ℝ) :
    (multiMomentumWightmanData hw q).W = multiMomentumW m w q := rfl

def wightmanConfigToUnit (A : WightmanConfig ι) : WightmanConfig Unit :=
  ⟨A.1, (default, A.2.2)⟩

theorem wightmanKernel_vectorMomentumW_eq (e q : Fin 4 → ℝ)
    (A B : WightmanConfig (Fin 4)) :
    wightmanKernel stdStarStructure (vectorMomentumW e q) A B =
      star (vectorPolarizationFactor e A.1 A.2.1) *
        vectorPolarizationFactor e B.1 B.2.1 *
        wightmanKernel trivialStarStructure (fourMomentumW q)
          (wightmanConfigToUnit A) (wightmanConfigToUnit B) := by
  unfold wightmanKernel
  rw [sum_prod_stdStarStructure_C_mul A.1 A.2.1, Fintype.sum_unique]
  have h_triv :
      (∏ i : Fin (wightmanConfigToUnit A).1,
        trivialStarStructure.C ((wightmanConfigToUnit A).2.1 i)
          ((default : Fin A.1 → Unit) i)) =
        1 := Finset.prod_eq_one (fun _ _ => rfl)
  rw [h_triv, one_mul]
  change vectorPolarizationFactor e (A.1 + B.1) (osConcatIdx A.1 B.1 A.2.1 B.2.1) *
      fourMomentumW q (A.1 + B.1) default
        (wightmanConcatSchwartz A.1 B.1 A.2.2 B.2.2) =
    star (vectorPolarizationFactor e A.1 A.2.1) *
      vectorPolarizationFactor e B.1 B.2.1 *
      fourMomentumW q (A.1 + B.1)
        (osConcatIdx A.1 B.1 default (wightmanConfigToUnit B).2.1)
        (wightmanConcatSchwartz A.1 B.1 A.2.2 B.2.2)
  have h_idx :
      osConcatIdx A.1 B.1 (default : Fin A.1 → Unit)
        (wightmanConfigToUnit B).2.1 = default :=
    Subsingleton.elim _ _
  rw [h_idx, vectorPolarizationFactor_osConcatIdx, star_vectorPolarizationFactor, mul_assoc]

theorem vectorMomentumWightmanHermiticity (e q : Fin 4 → ℝ) :
    WightmanKernelHermiticity stdStarStructure (vectorMomentumW e q) := by
  intro A B
  rw [wightmanKernel_vectorMomentumW_eq, wightmanKernel_vectorMomentumW_eq,
      star_mul', star_mul', star_star, star_vectorPolarizationFactor,
      fourMomentumWightmanHermiticity q (wightmanConfigToUnit A) (wightmanConfigToUnit B)]
  ring

theorem vectorMomentumWightmanPositive (e q : Fin 4 → ℝ) :
    WightmanKernelPositive stdStarStructure (vectorMomentumW e q) := by
  intro Ψ
  unfold wightmanPreInner Finsupp.sum
  simp_rw [wightmanKernel_vectorMomentumW_eq, wightmanKernel_fourMomentumW_eq]
  let f_even : WightmanConfig (Fin 4) → ℂ := fun A =>
    Ψ A * vectorPolarizationFactor e A.1 A.2.1 *
      fourMomentumEvenWightmanTerm q (wightmanConfigToUnit A)
  let f_odd : WightmanConfig (Fin 4) → ℂ := fun A =>
    Ψ A * vectorPolarizationFactor e A.1 A.2.1 *
      fourMomentumOddWightmanTerm q (wightmanConfigToUnit A)
  have h_split : ∀ A B : WightmanConfig (Fin 4),
      star (Ψ A) * Ψ B *
        (star (vectorPolarizationFactor e A.1 A.2.1) *
          vectorPolarizationFactor e B.1 B.2.1 *
          (star (fourMomentumEvenWightmanTerm q (wightmanConfigToUnit A)) *
            fourMomentumEvenWightmanTerm q (wightmanConfigToUnit B) +
          star (fourMomentumOddWightmanTerm q (wightmanConfigToUnit A)) *
            fourMomentumOddWightmanTerm q (wightmanConfigToUnit B))) =
      (starRingEnd ℂ) (f_even A) * f_even B +
        (starRingEnd ℂ) (f_odd A) * f_odd B := by
    intro A B
    dsimp [f_even, f_odd]
    simp only [map_mul]
    ring
  simp_rw [h_split, Finset.sum_add_distrib,
      sum_star_mul_eq_normSq Ψ.support f_even,
      sum_star_mul_eq_normSq Ψ.support f_odd]
  have h_nonneg : 0 ≤
      Complex.normSq (∑ A ∈ Ψ.support, f_even A) +
        Complex.normSq (∑ A ∈ Ψ.support, f_odd A) :=
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  exact_mod_cast h_nonneg

noncomputable def vectorMomentumWightmanData (e q : Fin 4 → ℝ) :
    WightmanPositiveData stdRep stdStarStructure where
  W := vectorMomentumW e q
  hermiticity := vectorMomentumWightmanHermiticity e q
  positivity := vectorMomentumWightmanPositive e q

@[simp]
lemma vectorMomentumWightmanData_W (e q : Fin 4 → ℝ) :
    (vectorMomentumWightmanData e q).W = vectorMomentumW e q := rfl

theorem phaseC_os_wightman_hilbert_bridge_master
    (q : Fin 4 → ℝ) {E : ℝ} (hE : 0 ≤ E) (e : Fin 4 → ℝ) :
    (fourMomentumOSWightmanLinearIsometryEquiv q
        (osVacuum (fourMomentumOSData q)) =
      wightmanVacuum (fourMomentumWightmanData q)) ∧
    (fourMomentumOSWightmanLinearIsometryEquiv q
        (fourMomentumOneParticle q) =
      fourMomentumWightmanOneParticle q) ∧
    (∀ x y : OSHilbert (fourMomentumOSData q),
      ⟪fourMomentumOSWightmanLinearIsometryEquiv q x,
        fourMomentumOSWightmanLinearIsometryEquiv q y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
    (∀ (α : Fin 2 → Unit) (z : Fin 2 → Fin 4 → ℂ),
      (fourMomentumOSSpectralDecomposition
          (by simpa [euclidTimeVec] using hE)).twoPointTubePropagator
        (fourMomentumOSTranslationInvariant (euclidTimeVec E))
        ((fourMomentumOSWightmanLinearIsometryEquiv (euclidTimeVec E)).symm
          (fourMomentumWightmanOneParticle (euclidTimeVec E)))
        ((fourMomentumOSWightmanLinearIsometryEquiv (euclidTimeVec E)).symm
          (fourMomentumWightmanOneParticle (euclidTimeVec E)))
        0 z =
        fourMomentumH (euclidTimeVec E) 2 α z) ∧
    WightmanKernelHermiticity stdStarStructure (vectorMomentumW e q) ∧
    WightmanKernelPositive stdStarStructure (vectorMomentumW e q) := by
  have hE0 : 0 ≤ euclidTimeVec E 0 := by simpa [euclidTimeVec] using hE
  have h_bridge : ∀ (α : Fin 2 → Unit) (z : Fin 2 → Fin 4 → ℂ),
      (fourMomentumOSSpectralDecomposition hE0).twoPointTubePropagator
        (fourMomentumOSTranslationInvariant (euclidTimeVec E))
        ((fourMomentumOSWightmanLinearIsometryEquiv (euclidTimeVec E)).symm
          (fourMomentumWightmanOneParticle (euclidTimeVec E)))
        ((fourMomentumOSWightmanLinearIsometryEquiv (euclidTimeVec E)).symm
          (fourMomentumWightmanOneParticle (euclidTimeVec E)))
        0 z =
        fourMomentumH (euclidTimeVec E) 2 α z := by
    intro α z
    have h_eq :=
      fourMomentumOSWightman_twoPointTubePropagator_bridge hE0
        (fourMomentumOSTranslationInvariant (euclidTimeVec E)) α z
    have h_vec : euclidTimeVec (euclidTimeVec E 0) = euclidTimeVec E := by
      ext μ
      fin_cases μ <;> simp [euclidTimeVec]
    rwa [h_vec] at h_eq
  exact ⟨fourMomentumOSWightmanLinearIsometryEquiv_osVacuum q,
    fourMomentumOSWightmanLinearIsometryEquiv_oneParticle q,
    fun x y => (fourMomentumOSWightmanLinearIsometryEquiv q).inner_map_map x y,
    h_bridge,
    vectorMomentumWightmanHermiticity e q,
    vectorMomentumWightmanPositive e q⟩

lemma complex_integral_nonneg {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {g : X → ℂ} (_hg : Integrable g ν) (hnn : ∀ x : X, 0 ≤ g x) :
    0 ≤ ∫ x : X, g x ∂ν := by
  have h_int_eq : (∫ x : X, g x ∂ν) = ∫ x : X, ((g x).re : ℂ) ∂ν :=
    integral_congr_ae (Filter.Eventually.of_forall (fun x =>
      Complex.ext rfl (Complex.nonneg_iff.mp (hnn x)).2.symm))
  rw [h_int_eq, integral_complex_ofReal]
  have h_re_nn : 0 ≤ ∫ x : X, (g x).re ∂ν :=
    integral_nonneg (fun x => (Complex.nonneg_iff.mp (hnn x)).1)
  exact_mod_cast h_re_nn

noncomputable def continuousMomentumMeasureFamily
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone) :
    ForwardConeSpectralMeasureFamily Unit where
  A _ := A₀
  instMeas _ := inferInstance
  μ _ := μ
  instSFinite _ := inferInstance
  ρ n _ a := if n % 2 = 0 then (w a : ℂ) else 0
  integrable_ρ n _ := by
    by_cases hn : n % 2 = 0
    · simp only [if_pos hn]
      exact Complex.ofRealCLM.integrable_comp hw_int
    · simp only [if_neg hn]
      exact integrable_zero _ _ _
  p n _ a := if n % 2 = 0 then alternatingMomentum n (q a) else 0
  measurable_p n _ := by
    by_cases hn : n % 2 = 0
    · simp only [if_pos hn]
      refine measurable_pi_lambda _ (fun i => ?_)
      unfold alternatingMomentum
      split_ifs
      · exact hq_meas
      · exact hq_meas.neg
    · simp only [if_neg hn]
      exact measurable_const
  mem_forwardCone n _ a := by
    by_cases hn : n % 2 = 0
    · rw [if_pos hn]
      exact alternatingMomentum_mem_forwardConeSpectralRegion n hn (hq_cone a)
    · rw [if_neg hn]
      exact zero_mem_forwardConeSpectralRegion n

noncomputable def continuousMomentumW
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone) :
    WightmanFamily Unit :=
  (continuousMomentumMeasureFamily μ hw_int hq_meas hq_cone).toWightmanFamily

noncomputable def continuousMomentumH
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone) :
    ∀ n : ℕ, (Fin n → Unit) → (Fin n → Fin 4 → ℂ) → ℂ :=
  (continuousMomentumMeasureFamily μ hw_int hq_meas hq_cone).H

noncomputable def continuousMomentumTubeExtension
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone) :
    TubeExtension (continuousMomentumW μ hw_int hq_meas hq_cone) :=
  (continuousMomentumMeasureFamily μ hw_int hq_meas hq_cone).toTubeExtension

noncomputable def continuousMomentumS
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone) :
    SchwingerFamily Unit :=
  (continuousMomentumMeasureFamily μ hw_int hq_meas hq_cone).toSchwingerFamily

@[simp]
theorem continuousMomentumTubeExtension_H
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone) :
    (continuousMomentumTubeExtension μ hw_int hq_meas hq_cone).H =
      continuousMomentumH μ hw_int hq_meas hq_cone := rfl

theorem integrable_continuousMomentumW_term
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone)
    (n : ℕ) (α : Fin n → Unit) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    Integrable (fun a : A₀ => (w a : ℂ) * fourMomentumW (q a) n α f) μ := by
  let F := continuousMomentumMeasureFamily μ hw_int hq_meas hq_cone
  have h_int : Integrable (fun a : A₀ => F.ρ n α a * minkowskiFourier f (F.p n α a)) μ :=
    F.integrable_ρ_mul_minkowskiFourier n α f
  refine h_int.congr (Filter.Eventually.of_forall (fun a => ?_))
  dsimp [F, continuousMomentumMeasureFamily]
  rw [fourMomentumW_apply]
  split_ifs <;> simp

theorem continuousMomentumW_apply_eq_integral_fourMomentumW
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone)
    (n : ℕ) (α : Fin n → Unit) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    continuousMomentumW μ hw_int hq_meas hq_cone n α f =
      ∫ a : A₀, (w a : ℂ) * fourMomentumW (q a) n α f ∂μ := by
  unfold continuousMomentumW
  rw [ForwardConeSpectralMeasureFamily.toWightmanFamily_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun a => ?_))
  dsimp [continuousMomentumMeasureFamily]
  rw [fourMomentumW_apply]
  split_ifs <;> simp

theorem integrable_continuousMomentumH_term
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone)
    (n : ℕ) (α : Fin n → Unit) {z : Fin n → Fin 4 → ℂ}
    (hz : z ∈ closed_forward_tube_n n) :
    Integrable (fun a : A₀ => (w a : ℂ) * fourMomentumH (q a) n α z) μ := by
  let F := continuousMomentumMeasureFamily μ hw_int hq_meas hq_cone
  have h_int : Integrable (fun a : A₀ => F.ρ n α a * vladimirov_kernel n z (F.p n α a)) μ :=
    F.integrable_ρ_mul_kernel_of_closed_forward_tube n α hz
  refine h_int.congr (Filter.Eventually.of_forall (fun a => ?_))
  dsimp [F, continuousMomentumMeasureFamily]
  unfold fourMomentumH
  split_ifs <;> simp

theorem continuousMomentumH_eq_integral_fourMomentumH
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone)
    (n : ℕ) (α : Fin n → Unit) (z : Fin n → Fin 4 → ℂ) :
    continuousMomentumH μ hw_int hq_meas hq_cone n α z =
      ∫ a : A₀, (w a : ℂ) * fourMomentumH (q a) n α z ∂μ := by
  unfold continuousMomentumH ForwardConeSpectralMeasureFamily.H
  refine integral_congr_ae (Filter.Eventually.of_forall (fun a => ?_))
  dsimp [continuousMomentumMeasureFamily]
  unfold fourMomentumH
  split_ifs <;> simp

theorem continuousMomentumS_apply_eq_integral_fourMomentumS
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone)
    (n : ℕ) (α : Fin n → Unit) (x : Fin n → Fin 4 → ℝ) :
    continuousMomentumS μ hw_int hq_meas hq_cone n α x =
      ∫ a : A₀, (w a : ℂ) * fourMomentumS (q a) n α x ∂μ :=
  continuousMomentumH_eq_integral_fourMomentumH μ hw_int hq_meas hq_cone n α
    (wickEmbedN n x)

@[simp]
theorem continuousMomentumH_zero
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone)
    (α : Fin 0 → Unit) (z : Fin 0 → Fin 4 → ℂ) :
    continuousMomentumH μ hw_int hq_meas hq_cone 0 α z =
      ((∫ a : A₀, w a ∂μ : ℝ) : ℂ) := by
  rw [continuousMomentumH_eq_integral_fourMomentumH]
  simp [integral_complex_ofReal]

@[simp]
theorem continuousMomentumS_zero
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone)
    (α : Fin 0 → Unit) (x : Fin 0 → Fin 4 → ℝ) :
    continuousMomentumS μ hw_int hq_meas hq_cone 0 α x =
      ((∫ a : A₀, w a ∂μ : ℝ) : ℂ) :=
  continuousMomentumH_zero μ hw_int hq_meas hq_cone α (wickEmbedN 0 x)

theorem continuousMomentumS_vacuumNormalized_iff
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone) :
    OSVacuumNormalized (continuousMomentumS μ hw_int hq_meas hq_cone) ↔
      ∫ a : A₀, w a ∂μ = 1 := by
  unfold OSVacuumNormalized
  rw [continuousMomentumS_zero]
  exact_mod_cast Iff.rfl

theorem continuousMomentumW_forwardConeSpectrumCondition
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone) :
    ForwardConeSpectrumCondition
      (continuousMomentumW μ hw_int hq_meas hq_cone) :=
  (continuousMomentumMeasureFamily μ hw_int hq_meas hq_cone).forwardConeSpectrumCondition

theorem continuousMomentumTubeTranslationInvariant
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone) :
    TubeTranslationInvariant
      (continuousMomentumTubeExtension μ hw_int hq_meas hq_cone) :=
  (continuousMomentumMeasureFamily μ hw_int hq_meas hq_cone).tubeTranslationInvariant

theorem continuousMomentumOSTranslationInvariant
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone) :
    OSTranslationInvariant (continuousMomentumS μ hw_int hq_meas hq_cone) :=
  schwingerFromTube_translation_invariant
    (continuousMomentumTubeExtension μ hw_int hq_meas hq_cone)
    (continuousMomentumTubeTranslationInvariant μ hw_int hq_meas hq_cone)

theorem continuousMomentumTubeWickHermiticity
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone) :
    TubeWickHermiticity trivialStarStructure
      (continuousMomentumTubeExtension μ hw_int hq_meas hq_cone) := by
  intro n α z _hz _hstar
  simp only [Fintype.sum_unique, trivialStarStructure, Matrix.one_apply_eq,
    Finset.prod_const_one, one_mul, continuousMomentumTubeExtension_H]
  rw [continuousMomentumH_eq_integral_fourMomentumH,
      continuousMomentumH_eq_integral_fourMomentumH,
      Complex.star_def, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun a => ?_))
  dsimp only
  rw [← Complex.star_def, star_mul', Complex.star_def, Complex.conj_ofReal,
      ← Complex.star_def, star_fourMomentumH_eq, Subsingleton.elim α (default ∘ Fin.rev)]

theorem continuousMomentumOSHermiticity
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone) :
    OSHermiticity trivialStarStructure
      (continuousMomentumS μ hw_int hq_meas hq_cone) :=
  schwingerFromTube_os_hermiticity trivialStarStructure
    (continuousMomentumTubeExtension μ hw_int hq_meas hq_cone)
    (continuousMomentumTubeWickHermiticity μ hw_int hq_meas hq_cone)

theorem continuousMomentumTubeWeakLocality_one
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone) :
    TubeWeakLocality 1
      (continuousMomentumTubeExtension μ hw_int hq_meas hq_cone) := by
  intro n α z hz
  rw [one_pow, one_mul]
  change continuousMomentumH μ hw_int hq_meas hq_cone n α (-(z ∘ Fin.rev)) =
    continuousMomentumH μ hw_int hq_meas hq_cone n (α ∘ Fin.rev) z
  rw [continuousMomentumH_eq_integral_fourMomentumH,
      continuousMomentumH_eq_integral_fourMomentumH]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun a => ?_))
  have ha := fourMomentumTubeWeakLocality_one (q a) n α z hz
  rw [one_pow, one_mul] at ha
  exact congrArg ((w a : ℂ) * ·) ha

theorem continuousMomentumOSSymmetric
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone)
    (n : ℕ) (α : Fin n → Unit) (x : Fin n → Fin 4 → ℝ)
    (hx : x ∈ orderedEuclidN n) :
    continuousMomentumS μ hw_int hq_meas hq_cone n α (-(x ∘ Fin.rev)) =
      (1 : ℂ) ^ (n * (n - 1) / 2) *
        continuousMomentumS μ hw_int hq_meas hq_cone n (α ∘ Fin.rev) x :=
  schwingerFromTube_weakLocality
    (continuousMomentumTubeExtension μ hw_int hq_meas hq_cone)
    (continuousMomentumTubeWeakLocality_one μ hw_int hq_meas hq_cone) n α x hx

theorem continuousMomentumW_pct
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone) :
    WightmanPCT 1 trivialRep (continuousMomentumW μ hw_int hq_meas hq_cone) :=
  wightman_pct_trivialRep_of_tube
    (continuousMomentumTubeExtension μ hw_int hq_meas hq_cone)
    (continuousMomentumTubeTranslationInvariant μ hw_int hq_meas hq_cone)
    (continuousMomentumTubeWeakLocality_one μ hw_int hq_meas hq_cone)

theorem continuousMomentumW_positivity
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ) (hw_nn : ∀ a : A₀, 0 ≤ w a)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone) :
    Positivity trivialStarStructure
      (continuousMomentumW μ hw_int hq_meas hq_cone) := by
  intro N F G hG
  have h_pair : ∀ j k : ℕ,
      (∑ α : Fin j → Unit, ∑ α' : Fin k → Unit, ∑ β : Fin j → Unit,
        (∏ i : Fin j, trivialStarStructure.C (α i) (β i)) *
          continuousMomentumW μ hw_int hq_meas hq_cone (j + k)
            (Fin.append (β ∘ Fin.rev) α') (G j k α α')) =
      ∫ a : A₀, (w a : ℂ) *
        (∑ α : Fin j → Unit, ∑ α' : Fin k → Unit, ∑ β : Fin j → Unit,
          (∏ i : Fin j, trivialStarStructure.C (α i) (β i)) *
            fourMomentumW (q a) (j + k)
              (Fin.append (β ∘ Fin.rev) α') (G j k α α')) ∂μ := by
    intro j k
    simp only [Fintype.sum_unique, trivialStarStructure, Matrix.one_apply_eq,
      Finset.prod_const_one, one_mul,
      continuousMomentumW_apply_eq_integral_fourMomentumW]
  simp_rw [h_pair]
  have h_int_pair : ∀ j k : ℕ,
      Integrable (fun a : A₀ => (w a : ℂ) *
        (∑ α : Fin j → Unit, ∑ α' : Fin k → Unit, ∑ β : Fin j → Unit,
          (∏ i : Fin j, trivialStarStructure.C (α i) (β i)) *
            fourMomentumW (q a) (j + k)
              (Fin.append (β ∘ Fin.rev) α') (G j k α α'))) μ := by
    intro j k
    simp only [Fintype.sum_unique, trivialStarStructure, Matrix.one_apply_eq,
      Finset.prod_const_one, one_mul]
    exact integrable_continuousMomentumW_term μ hw_int hq_meas hq_cone
      (j + k) (Fin.append (default ∘ Fin.rev) default) (G j k default default)
  have h_inner_sum : ∀ j ∈ Finset.range (N + 1),
      (∑ k ∈ Finset.range (N + 1),
        ∫ a : A₀, (w a : ℂ) *
          (∑ α : Fin j → Unit, ∑ α' : Fin k → Unit, ∑ β : Fin j → Unit,
            (∏ i : Fin j, trivialStarStructure.C (α i) (β i)) *
              fourMomentumW (q a) (j + k)
                (Fin.append (β ∘ Fin.rev) α') (G j k α α')) ∂μ) =
      ∫ a : A₀, ∑ k ∈ Finset.range (N + 1), (w a : ℂ) *
        (∑ α : Fin j → Unit, ∑ α' : Fin k → Unit, ∑ β : Fin j → Unit,
          (∏ i : Fin j, trivialStarStructure.C (α i) (β i)) *
            fourMomentumW (q a) (j + k)
              (Fin.append (β ∘ Fin.rev) α') (G j k α α')) ∂μ :=
    fun j _ => (integral_finsetSum (Finset.range (N + 1))
      (fun k _ => h_int_pair j k)).symm
  rw [Finset.sum_congr rfl h_inner_sum,
      ← integral_finsetSum (Finset.range (N + 1)) (fun j _ =>
        integrable_finsetSum (Finset.range (N + 1)) (fun k _ => h_int_pair j k))]
  have h_int_total :
      Integrable (fun a : A₀ => ∑ j ∈ Finset.range (N + 1),
        ∑ k ∈ Finset.range (N + 1), (w a : ℂ) *
          (∑ α : Fin j → Unit, ∑ α' : Fin k → Unit, ∑ β : Fin j → Unit,
            (∏ i : Fin j, trivialStarStructure.C (α i) (β i)) *
              fourMomentumW (q a) (j + k)
                (Fin.append (β ∘ Fin.rev) α') (G j k α α'))) μ :=
    integrable_finsetSum (Finset.range (N + 1)) (fun j _ =>
      integrable_finsetSum (Finset.range (N + 1)) (fun k _ => h_int_pair j k))
  refine complex_integral_nonneg h_int_total (fun a => ?_)
  simp_rw [← Finset.mul_sum]
  have h_wa : (0 : ℂ) ≤ (w a : ℂ) := by exact_mod_cast hw_nn a
  exact mul_nonneg h_wa (fourMomentumW_positivity (q a) N F G hG)

theorem integrable_osKernel_continuousMomentumS_term
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone)
    (A B : OSConfig Unit) :
    Integrable (fun a : A₀ =>
      (w a : ℂ) * osKernel trivialStarStructure (fourMomentumS (q a)) A B) μ := by
  rcases A with ⟨j, α, x, hx⟩
  rcases B with ⟨k, α', y, hy⟩
  unfold osKernel
  simp only [Fintype.sum_unique, trivialStarStructure, Matrix.one_apply_eq,
    Finset.prod_const_one, one_mul, fourMomentumS_apply]
  have h_ord : osConcatPoint j k x y ∈ orderedEuclidN (j + k) :=
    osConcatPoint_mem_orderedEuclidN j k hx hy
  have hz_cl : wickEmbedN (j + k) (osConcatPoint j k x y) ∈
      closed_forward_tube_n (j + k) :=
    forward_tube_n_subset_closed_forward_tube_n (j + k)
      (wickEmbedN_mem_forward_tube_n (j + k) h_ord)
  exact integrable_continuousMomentumH_term μ hw_int hq_meas hq_cone
    (j + k) (osConcatIdx j k default α') hz_cl

theorem osKernel_continuousMomentumS_eq
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone)
    (A B : OSConfig Unit) :
    osKernel trivialStarStructure
        (continuousMomentumS μ hw_int hq_meas hq_cone) A B =
      ∫ a : A₀, (w a : ℂ) *
        osKernel trivialStarStructure (fourMomentumS (q a)) A B ∂μ := by
  rcases A with ⟨j, α, x, hx⟩
  rcases B with ⟨k, α', y, hy⟩
  unfold osKernel
  simp only [Fintype.sum_unique, trivialStarStructure, Matrix.one_apply_eq,
    Finset.prod_const_one, one_mul,
    continuousMomentumS_apply_eq_integral_fourMomentumS]

theorem osPreInner_continuousMomentumS_eq
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone)
    (Ψ Φ : OSConfig Unit →₀ ℂ) :
    osPreInner trivialStarStructure
        (continuousMomentumS μ hw_int hq_meas hq_cone) Ψ Φ =
      ∫ a : A₀, (w a : ℂ) *
        osPreInner trivialStarStructure (fourMomentumS (q a)) Ψ Φ ∂μ := by
  unfold osPreInner Finsupp.sum
  simp_rw [osKernel_continuousMomentumS_eq μ hw_int hq_meas hq_cone]
  have h_pull_inner : ∀ A ∈ Ψ.support, ∀ B ∈ Φ.support,
      star (Ψ A) * Φ B *
        (∫ a : A₀, (w a : ℂ) *
          osKernel trivialStarStructure (fourMomentumS (q a)) A B ∂μ) =
      ∫ a : A₀, (w a : ℂ) *
        (star (Ψ A) * Φ B *
          osKernel trivialStarStructure (fourMomentumS (q a)) A B) ∂μ := by
    intro A _ B _
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun a => by ring))
  have h_sum1 : ∀ A ∈ Ψ.support,
      (∑ B ∈ Φ.support, star (Ψ A) * Φ B *
        (∫ a : A₀, (w a : ℂ) *
          osKernel trivialStarStructure (fourMomentumS (q a)) A B ∂μ)) =
      ∫ a : A₀, ∑ B ∈ Φ.support, (w a : ℂ) *
        (star (Ψ A) * Φ B *
          osKernel trivialStarStructure (fourMomentumS (q a)) A B) ∂μ := by
    intro A hA
    rw [Finset.sum_congr rfl (fun B hB => h_pull_inner A hA B hB),
        ← integral_finsetSum Φ.support (fun B _ => ?_)]
    have h_int := (integrable_osKernel_continuousMomentumS_term
      μ hw_int hq_meas hq_cone A B).const_mul (star (Ψ A) * Φ B)
    refine h_int.congr (Filter.Eventually.of_forall (fun a => ?_))
    dsimp only
    ring
  rw [Finset.sum_congr rfl h_sum1,
      ← integral_finsetSum Ψ.support (fun A _ => ?_)]
  · refine integral_congr_ae (Filter.Eventually.of_forall (fun a => ?_))
    dsimp only
    simp_rw [← Finset.mul_sum]
  · refine integrable_finsetSum Φ.support (fun B _ => ?_)
    have h_int := (integrable_osKernel_continuousMomentumS_term
      μ hw_int hq_meas hq_cone A B).const_mul (star (Ψ A) * Φ B)
    refine h_int.congr (Filter.Eventually.of_forall (fun a => ?_))
    dsimp only
    ring

theorem integrable_osPreInner_fourMomentumS_self
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone)
    (Ψ : OSConfig Unit →₀ ℂ) :
    Integrable (fun a : A₀ => (w a : ℂ) *
      osPreInner trivialStarStructure (fourMomentumS (q a)) Ψ Ψ) μ := by
  unfold osPreInner Finsupp.sum
  have h_eq : (fun a : A₀ => (w a : ℂ) *
      ∑ A ∈ Ψ.support, ∑ B ∈ Ψ.support, star (Ψ A) * Ψ B *
        osKernel trivialStarStructure (fourMomentumS (q a)) A B) =
      fun a : A₀ => ∑ A ∈ Ψ.support, ∑ B ∈ Ψ.support,
        (star (Ψ A) * Ψ B) * ((w a : ℂ) *
          osKernel trivialStarStructure (fourMomentumS (q a)) A B) := by
    ext a
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun A _ => Finset.sum_congr rfl (fun B _ => by ring))
  rw [h_eq]
  exact integrable_finsetSum Ψ.support (fun A _ =>
    integrable_finsetSum Ψ.support (fun B _ =>
      (integrable_osKernel_continuousMomentumS_term
        μ hw_int hq_meas hq_cone A B).const_mul (star (Ψ A) * Ψ B)))

theorem continuousMomentumOSReflectionPositive
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ) (hw_nn : ∀ a : A₀, 0 ≤ w a)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone) :
    OSReflectionPositive trivialStarStructure
      (continuousMomentumS μ hw_int hq_meas hq_cone) := by
  intro Ψ
  rw [osPreInner_continuousMomentumS_eq μ hw_int hq_meas hq_cone]
  have h_int := Complex.reCLM.integrable_comp
    (integrable_osPreInner_fourMomentumS_self μ hw_int hq_meas hq_cone Ψ)
  have h_re_int :
      (∫ a : A₀, (w a : ℂ) *
        osPreInner trivialStarStructure (fourMomentumS (q a)) Ψ Ψ ∂μ).re =
      ∫ a : A₀, ((w a : ℂ) *
        osPreInner trivialStarStructure (fourMomentumS (q a)) Ψ Ψ).re ∂μ :=
    (Complex.reCLM.integral_comp_comm
      (integrable_osPreInner_fourMomentumS_self μ hw_int hq_meas hq_cone Ψ)).symm
  rw [h_re_int]
  refine integral_nonneg (fun a => ?_)
  dsimp only
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (hw_nn a) (fourMomentumOSReflectionPositive (q a) Ψ)

noncomputable def continuousMomentumOSData
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ) (hw_nn : ∀ a : A₀, 0 ≤ w a)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone) :
    OSReflectionPositiveData trivialRep trivialStarStructure where
  𝒮 := continuousMomentumS μ hw_int hq_meas hq_cone
  hermiticity := continuousMomentumOSHermiticity μ hw_int hq_meas hq_cone
  positivity := continuousMomentumOSReflectionPositive μ hw_int hw_nn hq_meas hq_cone

theorem continuousMomentumOSDiagonalKernelBounded
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone) :
    OSDiagonalKernelBounded trivialStarStructure
      (continuousMomentumS μ hw_int hq_meas hq_cone) := by
  intro A
  let F := continuousMomentumMeasureFamily μ hw_int hq_meas hq_cone
  refine ⟨∫ a : A₀, ‖F.ρ (A.1 + A.1) default a‖ ∂μ, fun τ hτ => ?_⟩
  rcases A with ⟨j, α, x, hx⟩
  unfold osKernel
  dsimp only [osConfigTimeShift]
  simp only [Fintype.sum_unique, trivialStarStructure, Matrix.one_apply_eq,
    Finset.prod_const_one, one_mul]
  let y : Fin j → Fin 4 → ℝ := fun i => x i + euclidTimeVec τ
  have hy : y ∈ posOrderedEuclidN j := timeShift_mem_posOrderedEuclidN j hx hτ
  have h_ord : osConcatPoint j j y y ∈ orderedEuclidN (j + j) :=
    osConcatPoint_mem_orderedEuclidN j j hy hy
  have hz : wickEmbedN (j + j) (osConcatPoint j j y y) ∈ forward_tube_n (j + j) :=
    wickEmbedN_mem_forward_tube_n (j + j) h_ord
  have h_idx : osConcatIdx j j (default : Fin j → Unit) α = default :=
    Subsingleton.elim _ _
  change ‖F.H (j + j) (osConcatIdx j j default α)
    (wickEmbedN (j + j) (osConcatPoint j j y y))‖ ≤ _
  rw [h_idx]
  exact F.norm_H_le (j + j) default hz

theorem continuousMomentumOSContraction
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ) (hw_nn : ∀ a : A₀, 0 ≤ w a)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone) :
    OSContractionCondition
      (continuousMomentumOSData μ hw_int hw_nn hq_meas hq_cone) :=
  osContractionCondition_of_diagonalKernelBounded
    (continuousMomentumOSData μ hw_int hw_nn hq_meas hq_cone)
    (continuousMomentumOSTranslationInvariant μ hw_int hq_meas hq_cone)
    (continuousMomentumOSDiagonalKernelBounded μ hw_int hq_meas hq_cone)

theorem continuousMomentumH_two_euclidTimeVec_eq_measureKallenLehmannTube
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {E : A₀ → ℝ} (hE_meas : Measurable E) (hE_nn : ∀ a : A₀, 0 ≤ E a)
    (α : Fin 2 → Unit) (z : Fin 2 → Fin 4 → ℂ) :
    continuousMomentumH μ hw_int
      ((measurable_pi_lambda _ (fun μ' => by
        dsimp [euclidTimeVec]
        split_ifs
        · exact hE_meas
        · exact measurable_const)))
      (fun a => euclidTimeVec_mem_closure_forward_light_cone (hE_nn a))
      2 α z =
    measureKallenLehmannTube μ w E z := by
  rw [continuousMomentumH_eq_integral_fourMomentumH]
  unfold measureKallenLehmannTube
  refine integral_congr_ae (Filter.Eventually.of_forall (fun a => ?_))
  dsimp only
  rw [fourMomentumH_two_euclidTimeVec]

theorem continuousMomentumS_two_euclidTimeVec_eq_measureKallenLehmannEuclid
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ)
    {E : A₀ → ℝ} (hE_meas : Measurable E) (hE_nn : ∀ a : A₀, 0 ≤ E a)
    (α : Fin 2 → Unit) (x : Fin 2 → Fin 4 → ℝ) :
    continuousMomentumS μ hw_int
      ((measurable_pi_lambda _ (fun μ' => by
        dsimp [euclidTimeVec]
        split_ifs
        · exact hE_meas
        · exact measurable_const)))
      (fun a => euclidTimeVec_mem_closure_forward_light_cone (hE_nn a))
      2 α x =
    measureKallenLehmannEuclid μ w E x := by
  rw [continuousMomentumS_apply_eq_integral_fourMomentumS]
  unfold measureKallenLehmannEuclid
  refine integral_congr_ae (Filter.Eventually.of_forall (fun a => ?_))
  dsimp only
  rw [fourMomentumS_two_euclidTimeVec]

theorem continuousMomentumW_count_eq_multiMomentumW
    (m : ℕ) (w : Fin m → ℝ) (q : Fin m → Fin 4 → ℝ)
    (hq : ∀ r : Fin m, q r ∈ closure forward_light_cone) :
    continuousMomentumW (Measure.count : Measure (Fin m))
      (Integrable.of_finite : Integrable w Measure.count)
      (measurable_of_finite q) hq =
    multiMomentumW m w q := by
  funext n α
  ext f
  rw [continuousMomentumW_apply_eq_integral_fourMomentumW,
      integral_fintype_count, multiMomentumW_apply]

theorem continuousMomentumH_count_eq_multiMomentumH
    (m : ℕ) (w : Fin m → ℝ) (q : Fin m → Fin 4 → ℝ)
    (hq : ∀ r : Fin m, q r ∈ closure forward_light_cone) :
    continuousMomentumH (Measure.count : Measure (Fin m))
      (Integrable.of_finite : Integrable w Measure.count)
      (measurable_of_finite q) hq =
    multiMomentumH m w q := by
  funext n α z
  rw [continuousMomentumH_eq_integral_fourMomentumH, integral_fintype_count]
  rfl

theorem continuousMomentumS_count_eq_multiMomentumS
    (m : ℕ) (w : Fin m → ℝ) (q : Fin m → Fin 4 → ℝ)
    (hq : ∀ r : Fin m, q r ∈ closure forward_light_cone) :
    continuousMomentumS (Measure.count : Measure (Fin m))
      (Integrable.of_finite : Integrable w Measure.count)
      (measurable_of_finite q) hq =
    multiMomentumS m w q := by
  funext n α x
  rw [continuousMomentumS_apply_eq_integral_fourMomentumS,
      integral_fintype_count, multiMomentumS_apply]

theorem continuousMomentum_master
    {A₀ : Type} [MeasurableSpace A₀] (μ : Measure A₀) [SFinite μ]
    {w : A₀ → ℝ} (hw_int : Integrable w μ) (hw_nn : ∀ a : A₀, 0 ≤ w a)
    {q : A₀ → Fin 4 → ℝ} (hq_meas : Measurable q)
    (hq_cone : ∀ a : A₀, q a ∈ closure forward_light_cone) :
    ForwardConeSpectrumCondition
      (continuousMomentumW μ hw_int hq_meas hq_cone) ∧
    Positivity trivialStarStructure
      (continuousMomentumW μ hw_int hq_meas hq_cone) ∧
    WightmanPCT 1 trivialRep
      (continuousMomentumW μ hw_int hq_meas hq_cone) ∧
    TubeTranslationInvariant
      (continuousMomentumTubeExtension μ hw_int hq_meas hq_cone) ∧
    TubeWickHermiticity trivialStarStructure
      (continuousMomentumTubeExtension μ hw_int hq_meas hq_cone) ∧
    TubeWeakLocality 1
      (continuousMomentumTubeExtension μ hw_int hq_meas hq_cone) ∧
    OSTranslationInvariant
      (continuousMomentumS μ hw_int hq_meas hq_cone) ∧
    OSHermiticity trivialStarStructure
      (continuousMomentumS μ hw_int hq_meas hq_cone) ∧
    OSReflectionPositive trivialStarStructure
      (continuousMomentumS μ hw_int hq_meas hq_cone) ∧
    (OSVacuumNormalized (continuousMomentumS μ hw_int hq_meas hq_cone) ↔
      ∫ a : A₀, w a ∂μ = 1) ∧
    OSDiagonalKernelBounded trivialStarStructure
      (continuousMomentumS μ hw_int hq_meas hq_cone) ∧
    OSContractionCondition
      (continuousMomentumOSData μ hw_int hw_nn hq_meas hq_cone) :=
  ⟨continuousMomentumW_forwardConeSpectrumCondition μ hw_int hq_meas hq_cone,
   continuousMomentumW_positivity μ hw_int hw_nn hq_meas hq_cone,
   continuousMomentumW_pct μ hw_int hq_meas hq_cone,
   continuousMomentumTubeTranslationInvariant μ hw_int hq_meas hq_cone,
   continuousMomentumTubeWickHermiticity μ hw_int hq_meas hq_cone,
   continuousMomentumTubeWeakLocality_one μ hw_int hq_meas hq_cone,
   continuousMomentumOSTranslationInvariant μ hw_int hq_meas hq_cone,
   continuousMomentumOSHermiticity μ hw_int hq_meas hq_cone,
   continuousMomentumOSReflectionPositive μ hw_int hw_nn hq_meas hq_cone,
   continuousMomentumS_vacuumNormalized_iff μ hw_int hq_meas hq_cone,
   continuousMomentumOSDiagonalKernelBounded μ hw_int hq_meas hq_cone,
   continuousMomentumOSContraction μ hw_int hw_nn hq_meas hq_cone⟩

theorem weakLocality_of_tubePCT (R : HolomorphicLorentzRep ι)
    (W : WightmanFamily ι) {η : ℂ} (E : TubeExtension W)
    (h_cov : TubeCovariant R E) (hpct : TubePCT η R E) :
    WeakLocality η W := by
  have hexloc := (tubePCT_iff_extendedTubeWeakLocality R W E h_cov).mp hpct
  intro n α f f' hf_tsupp hf'
  have hf'_eq : f' = schwartzRevCLM n f := by
    ext x
    have h_inv := hf' (revCLE n x)
    have h_rev_inv : (fun i => (revCLE n x) (Fin.rev i)) = x := revCLE_involutive n x
    rw [h_rev_inv] at h_inv
    exact h_inv
  rw [hf'_eq]
  have h_compact : ∀ k : ℕ,
      W n α (schwartzCutoffSeq n f k) =
        η ^ (n * (n - 1) / 2) *
          W n (α ∘ Fin.rev) (schwartzRevCLM n (schwartzCutoffSeq n f k)) := by
    intro k
    let g := schwartzCutoffSeq n f k
    have hg_supp : HasCompactSupport (g : (Fin n → Fin 4 → ℝ) → ℂ) :=
      schwartzCutoffSeq_hasCompactSupport n f k
    have hg_tsupp : tsupport (g : (Fin n → Fin 4 → ℝ) → ℂ) ⊆ jost_points_n n := by
      have h_mul : (g : (Fin n → Fin 4 → ℝ) → ℂ) =
          fun y => vladimirov_cutoff_bump_schwartz n ((((k : ℝ) + 1)⁻¹) • y) * f y := rfl
      rw [h_mul]
      exact tsupport_mul_subset_right.trans hf_tsupp
    have hg_ext : ∀ x ∈ tsupport (g : (Fin n → Fin 4 → ℝ) → ℂ),
        coeReal n x ∈ extended_tube_n n :=
      fun x hx => coeReal_mem_extended_tube_of_mem_jost_points n (hg_tsupp hx)
    let g' := schwartzRevCLM n g
    have hg'_supp : HasCompactSupport (g' : (Fin n → Fin 4 → ℝ) → ℂ) :=
      hasCompactSupport_schwartzRevCLM n hg_supp
    have hg'_ext : ∀ y ∈ tsupport (g' : (Fin n → Fin 4 → ℝ) → ℂ),
        coeReal n y ∈ extended_tube_n n := by
      intro y hy
      have hy_rev : revCLE n y ∈ tsupport (g : (Fin n → Fin 4 → ℝ) → ℂ) :=
        mem_tsupport_of_comp_continuous (revCLE n).continuous hy
      have h_rev_mem := rev_mem_extended_tube_n_of_mem n (hg_ext (revCLE n y) hy_rev)
      have h_coe : ((coeReal n (revCLE n y)) ∘ Fin.rev) = coeReal n y := by
        ext i μ
        simp [coeReal, revCLE_apply, Fin.rev_rev]
      rwa [h_coe] at h_rev_mem
    rw [W_eq_integral_spinor_H_ext_of_compactSupport_subset_extended_tube
          R W E h_cov n α g hg_supp hg_ext,
        W_eq_integral_spinor_H_ext_of_compactSupport_subset_extended_tube
          R W E h_cov n (α ∘ Fin.rev) g' hg'_supp hg'_ext,
        ← integral_comp_rev n (fun y : Fin n → Fin 4 → ℝ =>
          spinor_H_ext R W E n (α ∘ Fin.rev) (coeReal n y) * g' y),
        ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    by_cases hx : x ∈ tsupport (g : (Fin n → Fin 4 → ℝ) → ℂ)
    · have h_eq_ext := hexloc n α (coeReal n x) (hg_ext x hx)
      have h_coe_rev : (coeReal n x ∘ Fin.rev) = coeReal n (fun i => x (Fin.rev i)) := rfl
      have h_inv_x : (fun i : Fin n => x (Fin.rev (Fin.rev i))) = x := by
        ext i μ
        simp [Fin.rev_rev]
      dsimp [g', schwartzRevCLM_apply]
      rw [h_eq_ext, h_coe_rev, h_inv_x, mul_assoc]
    · have hg0 : g x = 0 := image_eq_zero_of_notMem_tsupport hx
      have h_inv_x : (fun i : Fin n => x (Fin.rev (Fin.rev i))) = x := by
        ext i μ
        simp [Fin.rev_rev]
      dsimp [g', schwartzRevCLM_apply]
      rw [h_inv_x, hg0, mul_zero, mul_zero, mul_zero]
  have h_seq := schwartzCutoffSeq_tendsto n f
  have h_lhs : Tendsto (fun k : ℕ => W n α (schwartzCutoffSeq n f k))
      Filter.atTop (𝓝 (W n α f)) :=
    ((W n α).continuous.tendsto f).comp h_seq
  have h_rhs : Tendsto
      (fun k : ℕ => η ^ (n * (n - 1) / 2) *
        W n (α ∘ Fin.rev) (schwartzRevCLM n (schwartzCutoffSeq n f k)))
      Filter.atTop
      (𝓝 (η ^ (n * (n - 1) / 2) * W n (α ∘ Fin.rev) (schwartzRevCLM n f))) :=
    (((W n (α ∘ Fin.rev)).continuous.tendsto _).comp
      (((schwartzRevCLM n).continuous.tendsto f).comp h_seq)).const_mul
        (η ^ (n * (n - 1) / 2))
  have h_eq :
      (fun k : ℕ => W n α (schwartzCutoffSeq n f k)) =
      fun k : ℕ => η ^ (n * (n - 1) / 2) *
        W n (α ∘ Fin.rev) (schwartzRevCLM n (schwartzCutoffSeq n f k)) :=
    funext h_compact
  exact tendsto_nhds_unique h_lhs (h_eq ▸ h_rhs)

theorem tubePCT_iff_weakLocality (R : HolomorphicLorentzRep ι)
    (W : WightmanFamily ι) {η : ℂ} (E : TubeExtension W)
    (h_cov : TubeCovariant R E) :
    TubePCT η R E ↔ WeakLocality η W :=
  ⟨weakLocality_of_tubePCT R W E h_cov,
   tubePCT_of_weakLocality R W E h_cov⟩

theorem spin_statistics_of_tubePCT_and_weakLocality
    (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι) {η ε : ℂ} (E : TubeExtension W)
    (h_cov : TubeCovariant R E) (hpct : TubePCT ε R E)
    (hloc : WeakLocality η W) (h_nondeg : ∃ β : Fin 2 → ι, W 2 β ≠ 0) :
    η = ε := by
  obtain ⟨β, hW_ne⟩ := h_nondeg
  have hH_ne : ∃ z : Fin 2 → Fin 4 → ℂ, z ∈ forward_tube_n 2 ∧ E.H 2 β z ≠ 0 := by
    by_contra h_all_zero
    push Not at h_all_zero
    apply hW_ne
    ext f
    have hv : unit_time_vector ∈ forward_light_cone := unit_time_vector_mem_forward_light_cone
    have hb := E.boundary 2 β f unit_time_vector hv
    have h_ev :
        (fun t : ℝ => ∫ x : Fin 2 → Fin 4 → ℝ,
          E.H 2 β (fun i k => (x i k : ℂ) +
            Complex.I * ((t * (i : ℕ) * unit_time_vector k : ℝ) : ℂ)) * f x) =ᶠ[
              𝓝[>] (0 : ℝ)]
        fun _ : ℝ => (0 : ℂ) := by
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      refine MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall (fun x => ?_))
      simp only [Pi.zero_apply]
      rw [h_all_zero _ (line_mem_forward_tube 2 x unit_time_vector hv t ht), zero_mul]
    haveI : Filter.NeBot (𝓝[>] (0 : ℝ)) := nhdsWithin_Ioi_neBot le_rfl
    exact tendsto_nhds_unique hb ((tendsto_const_nhds (x := (0 : ℂ))).congr' h_ev.symm)
  rcases hH_ne with ⟨z, hz, hz_ne⟩
  let α : Fin 2 → ι := β ∘ Fin.rev
  have hα_rev : α ∘ Fin.rev = β := by
    ext i
    simp [α, Fin.rev_rev]
  have hw : (z ∘ Fin.rev) ∈ extended_tube_n 2 := rev_mem_extended_tube_n 2 z hz
  have hw_rev : ((z ∘ Fin.rev) ∘ Fin.rev) = z := by
    ext i k
    simp [Fin.rev_rev]
  have hex_eps := (tubePCT_iff_extendedTubeWeakLocality R W E h_cov).mp hpct 2 α
    (z ∘ Fin.rev) hw
  have hex_eta := (tubePCT_iff_extendedTubeWeakLocality R W E h_cov).mp
    (tubePCT_of_weakLocality R W E h_cov hloc) 2 α (z ∘ Fin.rev) hw
  have h_pow : (2 * (2 - 1) / 2 : ℕ) = 1 := rfl
  rw [h_pow, pow_one, hα_rev, hw_rev,
      spinor_H_ext_eq_on_forward_tube R W E h_cov 2 β hz] at hex_eps hex_eta
  exact mul_right_cancel₀ hz_ne (hex_eta.symm.trans hex_eps)

def massShellSpatialSq (p : Fin 3 → ℝ) : ℝ :=
  (p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2

lemma massShellSpatialSq_nonneg (p : Fin 3 → ℝ) : 0 ≤ massShellSpatialSq p := by
  unfold massShellSpatialSq
  positivity

noncomputable def massShellEnergy (m : ℝ) (p : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (m ^ 2 + massShellSpatialSq p)

noncomputable def massShellVec (m : ℝ) (p : Fin 3 → ℝ) : Fin 4 → ℝ :=
  ![massShellEnergy m p, p 0, p 1, p 2]

lemma massShellEnergy_sq (m : ℝ) (p : Fin 3 → ℝ) :
    (massShellEnergy m p) ^ 2 = m ^ 2 + massShellSpatialSq p :=
  Real.sq_sqrt (add_nonneg (sq_nonneg m) (massShellSpatialSq_nonneg p))

lemma massShellEnergy_ge_mass {m : ℝ} (hm : 0 < m) (p : Fin 3 → ℝ) :
    m ≤ massShellEnergy m p := by
  unfold massShellEnergy
  have h_le : m ^ 2 ≤ m ^ 2 + massShellSpatialSq p :=
    le_add_of_nonneg_right (massShellSpatialSq_nonneg p)
  calc m = Real.sqrt (m ^ 2) := (Real.sqrt_sq hm.le).symm
    _ ≤ Real.sqrt (m ^ 2 + massShellSpatialSq p) := Real.sqrt_le_sqrt h_le

lemma massShellEnergy_pos {m : ℝ} (hm : 0 < m) (p : Fin 3 → ℝ) :
    0 < massShellEnergy m p :=
  hm.trans_le (massShellEnergy_ge_mass hm p)

lemma abs_coord_le_massShellEnergy {m : ℝ} (hm : 0 < m) (p : Fin 3 → ℝ) (j : Fin 3) :
    |p j| ≤ massShellEnergy m p := by
  have h_pos := (massShellEnergy_pos hm p).le
  have h_sq : (p j) ^ 2 ≤ (massShellEnergy m p) ^ 2 := by
    rw [massShellEnergy_sq]
    unfold massShellSpatialSq
    rcases j with ⟨_ | _ | _ | k, hk⟩
    · change (p 0) ^ 2 ≤ m ^ 2 + ((p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2)
      nlinarith [sq_nonneg m, sq_nonneg (p 1), sq_nonneg (p 2)]
    · change (p 1) ^ 2 ≤ m ^ 2 + ((p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2)
      nlinarith [sq_nonneg m, sq_nonneg (p 0), sq_nonneg (p 2)]
    · change (p 2) ^ 2 ≤ m ^ 2 + ((p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2)
      nlinarith [sq_nonneg m, sq_nonneg (p 0), sq_nonneg (p 1)]
    · omega
  calc |p j| = Real.sqrt ((p j) ^ 2) := (Real.sqrt_sq_eq_abs (p j)).symm
    _ ≤ Real.sqrt ((massShellEnergy m p) ^ 2) := Real.sqrt_le_sqrt h_sq
    _ = massShellEnergy m p := Real.sqrt_sq h_pos

lemma norm_le_massShellEnergy {m : ℝ} (hm : 0 < m) (p : Fin 3 → ℝ) :
    ‖p‖ ≤ massShellEnergy m p :=
  (pi_norm_le_iff_of_nonneg (massShellEnergy_pos hm p).le).mpr
    (fun j => by simpa [Real.norm_eq_abs] using abs_coord_le_massShellEnergy hm p j)

lemma one_add_norm_le_scale_massShellEnergy {m : ℝ} (hm : 0 < m) (p : Fin 3 → ℝ) :
    1 + ‖p‖ ≤ (1 / m + 1) * massShellEnergy m p := by
  have h1 : 1 ≤ (1 / m) * massShellEnergy m p := by
    have h_mul := mul_le_mul_of_nonneg_left (massShellEnergy_ge_mass hm p)
      (one_div_nonneg.mpr hm.le)
    rwa [one_div_mul_cancel hm.ne'] at h_mul
  linarith [norm_le_massShellEnergy hm p]

@[simp]
lemma minkowskiInner_massShellVec_self (m : ℝ) (p : Fin 3 → ℝ) :
    minkowskiInner (massShellVec m p) (massShellVec m p) = m ^ 2 := by
  rw [minkowskiInner_explicit]
  dsimp [massShellVec]
  have h_sq := massShellEnergy_sq m p
  unfold massShellSpatialSq at h_sq
  nlinarith

theorem massShellVec_mem_forward_light_cone {m : ℝ} (hm : 0 < m) (p : Fin 3 → ℝ) :
    massShellVec m p ∈ forward_light_cone :=
  ⟨massShellEnergy_pos hm p, by
    rw [minkowskiInner_massShellVec_self]
    exact sq_pos_of_pos hm⟩

theorem massShellVec_mem_closure_forward_light_cone {m : ℝ} (hm : 0 < m)
    (p : Fin 3 → ℝ) :
    massShellVec m p ∈ closure forward_light_cone :=
  subset_closure (massShellVec_mem_forward_light_cone hm p)

lemma continuous_massShellEnergy (m : ℝ) : Continuous (massShellEnergy m) := by
  unfold massShellEnergy massShellSpatialSq
  refine Real.continuous_sqrt.comp (continuous_const.add ?_)
  exact (((continuous_apply 0).pow 2).add ((continuous_apply 1).pow 2)).add
    ((continuous_apply 2).pow 2)

lemma continuous_massShellVec (m : ℝ) : Continuous (massShellVec m) := by
  refine continuous_pi (fun μ => ?_)
  fin_cases μ
  · exact continuous_massShellEnergy m
  · exact continuous_apply 0
  · exact continuous_apply 1
  · exact continuous_apply 2

noncomputable def massShellBoost (m : ℝ) (A : SL2C) (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun j => ((lorentzOfSL2C A).mulVec (massShellVec m p)) j.succ

theorem lorentzOfSL2C_mulVec_massShellVec {m : ℝ} (hm : 0 < m) (A : SL2C)
    (p : Fin 3 → ℝ) :
    (lorentzOfSL2C A).mulVec (massShellVec m p) =
      massShellVec m (massShellBoost m A p) := by
  let w : Fin 4 → ℝ := (lorentzOfSL2C A).mulVec (massShellVec m p)
  have hw_cone : w ∈ forward_light_cone :=
    lorentzOfSL2C_preserves_forward_light_cone A (massShellVec_mem_forward_light_cone hm p)
  have hw_inner : minkowskiInner w w = m ^ 2 := by
    dsimp [w]
    rw [minkowskiInner_lorentz A, minkowskiInner_massShellVec_self]
  have hw0_sq : (w 0) ^ 2 = m ^ 2 + massShellSpatialSq (massShellBoost m A p) := by
    rw [minkowskiInner_explicit] at hw_inner
    unfold massShellSpatialSq massShellBoost
    change w 0 * w 0 - w 1 * w 1 - w 2 * w 2 - w 3 * w 3 = m ^ 2 at hw_inner
    dsimp [w] at hw_inner ⊢
    nlinarith
  have hw0 : w 0 = massShellEnergy m (massShellBoost m A p) := by
    calc w 0 = Real.sqrt ((w 0) ^ 2) := (Real.sqrt_sq hw_cone.1.le).symm
      _ = massShellEnergy m (massShellBoost m A p) := by
          unfold massShellEnergy
          rw [hw0_sq]
  ext μ
  fin_cases μ
  · exact hw0
  · simp [massShellVec, massShellBoost]
  · simp [massShellVec, massShellBoost]
  · simp [massShellVec, massShellBoost]

@[simp]
theorem massShellBoost_mul {m : ℝ} (hm : 0 < m) (A B : SL2C) (p : Fin 3 → ℝ) :
    massShellBoost m (A * B) p = massShellBoost m A (massShellBoost m B p) := by
  ext j
  simp only [massShellBoost, lorentzOfSL2C_mul, ← Matrix.mulVec_mulVec,
    lorentzOfSL2C_mulVec_massShellVec hm B p]

@[simp]
theorem massShellBoost_one (m : ℝ) (p : Fin 3 → ℝ) :
    massShellBoost m 1 p = p := by
  ext j
  fin_cases j <;> simp [massShellBoost, lorentzOfSL2C_one, massShellVec]

theorem massShellBoost_inv_comp {m : ℝ} (hm : 0 < m) (A : SL2C) (p : Fin 3 → ℝ) :
    massShellBoost m A⁻¹ (massShellBoost m A p) = p := by
  rw [← massShellBoost_mul hm, inv_mul_cancel, massShellBoost_one]

theorem massShellBoost_comp_inv {m : ℝ} (hm : 0 < m) (A : SL2C) (p : Fin 3 → ℝ) :
    massShellBoost m A (massShellBoost m A⁻¹ p) = p := by
  rw [← massShellBoost_mul hm, mul_inv_cancel, massShellBoost_one]

theorem massShellBoost_injOn {m : ℝ} (hm : 0 < m) (A : SL2C) :
    Set.InjOn (massShellBoost m A) Set.univ := by
  intro p _ q _ h_eq
  have h := congrArg (massShellBoost m A⁻¹) h_eq
  rwa [massShellBoost_inv_comp hm A, massShellBoost_inv_comp hm A] at h

theorem massShellBoost_image_univ {m : ℝ} (hm : 0 < m) (A : SL2C) :
    (massShellBoost m A) '' Set.univ = Set.univ := by
  ext q
  simp only [Set.mem_image, Set.mem_univ, true_and, iff_true]
  exact ⟨massShellBoost m A⁻¹ q, massShellBoost_comp_inv hm A q⟩

noncomputable def massShellEnergyDerivCLM (m : ℝ) (p : Fin 3 → ℝ) :
    (Fin 3 → ℝ) →L[ℝ] ℝ :=
  (massShellEnergy m p)⁻¹ •
    (p 0 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0 +
      p 1 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1 +
      p 2 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2)

theorem hasFDerivAt_massShellEnergy {m : ℝ} (hm : 0 < m) (p : Fin 3 → ℝ) :
    HasFDerivAt (massShellEnergy m) (massShellEnergyDerivCLM m p) p := by
  let pr := fun j : Fin 3 => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j
  have h0 := ((pr 0).hasFDerivAt (x := p)).pow 2
  have h1 := ((pr 1).hasFDerivAt (x := p)).pow 2
  have h2 := ((pr 2).hasFDerivAt (x := p)).pow 2
  have h_sum : HasFDerivAt (fun q : Fin 3 → ℝ => m ^ 2 + massShellSpatialSq q) _ p :=
    (hasFDerivAt_const (m ^ 2) p).add ((h0.add h1).add h2)
  have h_ne : m ^ 2 + massShellSpatialSq p ≠ 0 := by
    have h_pos : 0 < m ^ 2 + massShellSpatialSq p :=
      add_pos_of_pos_of_nonneg (sq_pos_of_pos hm) (massShellSpatialSq_nonneg p)
    exact h_pos.ne'
  refine (h_sum.sqrt h_ne).congr_fderiv ?_
  ext v
  have hω : Real.sqrt (m ^ 2 + massShellSpatialSq p) ≠ 0 := (massShellEnergy_pos hm p).ne'
  simp [massShellEnergyDerivCLM, massShellEnergy, pr]
  field_simp [hω]

noncomputable def massShellVecDerivCLM (m : ℝ) (p : Fin 3 → ℝ) :
    (Fin 3 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
  ContinuousLinearMap.pi
    ![massShellEnergyDerivCLM m p,
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0,
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1,
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2]

theorem hasFDerivAt_massShellVec {m : ℝ} (hm : 0 < m) (p : Fin 3 → ℝ) :
    HasFDerivAt (massShellVec m) (massShellVecDerivCLM m p) p := by
  refine hasFDerivAt_pi.mpr ?_
  refine Fin.forall_fin_succ.mpr ⟨hasFDerivAt_massShellEnergy hm p, ?_⟩
  refine Fin.forall_fin_succ.mpr
    ⟨(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).hasFDerivAt, ?_⟩
  refine Fin.forall_fin_succ.mpr
    ⟨(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1).hasFDerivAt, ?_⟩
  refine Fin.forall_fin_succ.mpr
    ⟨(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2).hasFDerivAt,
      fun x => x.elim0⟩

noncomputable def lorentzSingleCLM (A : SL2C) : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (lorentzOfSL2C A))

noncomputable def massShellSpatialProjCLM : (Fin 4 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi (fun j : Fin 3 =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) j.succ)

noncomputable def massShellBoostDerivCLM (m : ℝ) (A : SL2C) (p : Fin 3 → ℝ) :
    (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  massShellSpatialProjCLM.comp ((lorentzSingleCLM A).comp (massShellVecDerivCLM m p))

theorem hasFDerivAt_massShellBoost {m : ℝ} (hm : 0 < m) (A : SL2C) (p : Fin 3 → ℝ) :
    HasFDerivAt (massShellBoost m A) (massShellBoostDerivCLM m A p) p := by
  have h_eq : massShellBoost m A =
      fun q : Fin 3 → ℝ => massShellSpatialProjCLM (lorentzSingleCLM A (massShellVec m q)) :=
    rfl
  rw [h_eq]
  exact (massShellSpatialProjCLM.comp (lorentzSingleCLM A)).hasFDerivAt.comp p
    (hasFDerivAt_massShellVec hm p)

theorem lorentzSingleCLM_comp_massShellVecDerivCLM {m : ℝ} (hm : 0 < m) (A : SL2C)
    (p : Fin 3 → ℝ) :
    (lorentzSingleCLM A).comp (massShellVecDerivCLM m p) =
      (massShellVecDerivCLM m (massShellBoost m A p)).comp
        (massShellBoostDerivCLM m A p) := by
  have h_lhs : HasFDerivAt
      (fun q : Fin 3 → ℝ => lorentzSingleCLM A (massShellVec m q))
      ((lorentzSingleCLM A).comp (massShellVecDerivCLM m p)) p :=
    (lorentzSingleCLM A).hasFDerivAt.comp p (hasFDerivAt_massShellVec hm p)
  have h_rhs : HasFDerivAt
      (fun q : Fin 3 → ℝ => massShellVec m (massShellBoost m A q))
      ((massShellVecDerivCLM m (massShellBoost m A p)).comp
        (massShellBoostDerivCLM m A p)) p :=
    (hasFDerivAt_massShellVec hm (massShellBoost m A p)).comp p
      (hasFDerivAt_massShellBoost hm A p)
  have h_fn : (fun q : Fin 3 → ℝ => lorentzSingleCLM A (massShellVec m q)) =
      fun q : Fin 3 → ℝ => massShellVec m (massShellBoost m A q) := by
    ext q μ
    exact congr_fun (lorentzOfSL2C_mulVec_massShellVec hm A q) μ
  rw [h_fn] at h_lhs
  exact h_lhs.unique h_rhs

noncomputable def massShellFrame (m : ℝ) (p : Fin 3 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of (fun (μ ν : Fin 4) =>
    Fin.cases (massShellVec m p μ)
      (fun k => massShellVecDerivCLM m p (Pi.single k 1) μ) ν)

theorem det_massShellFrame {m : ℝ} (hm : 0 < m) (p : Fin 3 → ℝ) :
    (massShellFrame m p).det = m ^ 2 / massShellEnergy m p := by
  have he0 : massShellEnergy m p ≠ 0 := (massShellEnergy_pos hm p).ne'
  have h_sq := massShellEnergy_sq m p
  unfold massShellSpatialSq at h_sq
  let e0 := massShellEnergy m p
  have hF : massShellFrame m p =
      !![e0, e0⁻¹ * p 0, e0⁻¹ * p 1, e0⁻¹ * p 2;
         p 0, 1, 0, 0;
         p 1, 0, 1, 0;
         p 2, 0, 0, 1] := by
    ext i j
    refine Fin.cases ?_ (fun k => ?_) j
    · revert i
      refine Fin.forall_fin_succ.mpr ⟨?_, Fin.forall_fin_succ.mpr
        ⟨?_, Fin.forall_fin_succ.mpr
          ⟨?_, Fin.forall_fin_succ.mpr ⟨?_, fun x => x.elim0⟩⟩⟩⟩ <;>
        simp [e0, massShellFrame, massShellVec]
    · simp only [massShellFrame, Matrix.of_apply, Fin.cases_succ]
      revert i k
      refine Fin.forall_fin_succ.mpr ⟨?_, Fin.forall_fin_succ.mpr
        ⟨?_, Fin.forall_fin_succ.mpr
          ⟨?_, Fin.forall_fin_succ.mpr ⟨?_, fun x => x.elim0⟩⟩⟩⟩ <;>
        refine Fin.forall_fin_succ.mpr ⟨?_, Fin.forall_fin_succ.mpr
          ⟨?_, Fin.forall_fin_succ.mpr ⟨?_, fun y => y.elim0⟩⟩⟩ <;>
        simp [e0, massShellVecDerivCLM, massShellEnergyDerivCLM]
  rw [hF, Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp [Matrix.det_fin_three, Matrix.submatrix, Fin.succAbove]
  dsimp [e0]
  field_simp [he0]
  linarith

def massShellBoostBlock (J : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of (fun (μ ν : Fin 4) =>
    Fin.cases
      (Fin.cases 1 (fun _ => 0) ν)
      (fun i => Fin.cases 0 (fun j => J i j) ν)
      μ)

theorem det_massShellBoostBlock (J : Matrix (Fin 3) (Fin 3) ℝ) :
    (massShellBoostBlock J).det = J.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  have h_sub : (massShellBoostBlock J).submatrix Fin.succ (Fin.succAbove 0) = J := by
    ext i j
    simp [massShellBoostBlock]
  have h00 : massShellBoostBlock J 0 0 = 1 := rfl
  have h01 : massShellBoostBlock J 0 1 = 0 := rfl
  have h02 : massShellBoostBlock J 0 2 = 0 := rfl
  have h03 : massShellBoostBlock J 0 3 = 0 := rfl
  rw [h00, h01, h02, h03, h_sub]
  simp

theorem lorentzOfSL2C_mul_massShellFrame {m : ℝ} (hm : 0 < m) (A : SL2C)
    (p : Fin 3 → ℝ) :
    lorentzOfSL2C A * massShellFrame m p =
      massShellFrame m (massShellBoost m A p) *
        massShellBoostBlock
          (LinearMap.toMatrix' (massShellBoostDerivCLM m A p).toLinearMap) := by
  let L' := massShellBoostDerivCLM m A p
  have h_chain := lorentzSingleCLM_comp_massShellVecDerivCLM hm A p
  ext μ ν
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Fin.cases ?_ (fun k => ?_) ν
  · have h_lhs :
        (∑ ρ : Fin 4, lorentzOfSL2C A μ ρ * massShellFrame m p ρ 0) =
          ((lorentzOfSL2C A).mulVec (massShellVec m p)) μ := rfl
    rw [h_lhs, lorentzOfSL2C_mulVec_massShellVec hm A p, Fin.sum_univ_succ]
    simp [massShellFrame, massShellBoostBlock]
  · have h_lhs :
        (∑ ρ : Fin 4, lorentzOfSL2C A μ ρ * massShellFrame m p ρ k.succ) =
          ((lorentzSingleCLM A).comp (massShellVecDerivCLM m p))
            (Pi.single k 1) μ := rfl
    rw [h_lhs, h_chain]
    change (massShellVecDerivCLM m (massShellBoost m A p)) (L' (Pi.single k 1)) μ = _
    have h_vec_expand : L' (Pi.single k 1) =
        ∑ r : Fin 3, (L' (Pi.single k 1) r) • Pi.single r (1 : ℝ) := by
      ext r
      simp [Finset.sum_apply, Pi.single_apply]
    rw [h_vec_expand, map_sum, Finset.sum_apply]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [massShellFrame, massShellBoostBlock, Matrix.of_apply,
      Fin.cases_zero, Fin.cases_succ, mul_zero, zero_add, ContinuousLinearMap.map_smul,
      Pi.smul_apply, smul_eq_mul, LinearMap.toMatrix'_apply,
      ContinuousLinearMap.coe_coe]
    exact Finset.sum_congr rfl (fun (i : Fin 3) _ => mul_comm _ _)

theorem det_massShellBoostDerivCLM {m : ℝ} (hm : 0 < m) (A : SL2C) (p : Fin 3 → ℝ) :
    (massShellBoostDerivCLM m A p).det =
      massShellEnergy m (massShellBoost m A p) / massShellEnergy m p := by
  let L' := massShellBoostDerivCLM m A p
  let J := LinearMap.toMatrix' L'.toLinearMap
  have h_mat := congrArg Matrix.det (lorentzOfSL2C_mul_massShellFrame hm A p)
  rw [Matrix.det_mul, Matrix.det_mul, lorentzOfSL2C_det_one A, one_mul,
      det_massShellFrame hm p, det_massShellFrame hm (massShellBoost m A p),
      det_massShellBoostBlock] at h_mat
  have h_clm_det : L'.det = J.det :=
    (LinearMap.det_toMatrix' L'.toLinearMap).symm
  rw [h_clm_det]
  have hm2 : m ^ 2 ≠ 0 := (sq_pos_of_pos hm).ne'
  have hω1 : massShellEnergy m p ≠ 0 := (massShellEnergy_pos hm p).ne'
  have hω2 : massShellEnergy m (massShellBoost m A p) ≠ 0 :=
    (massShellEnergy_pos hm (massShellBoost m A p)).ne'
  have h_eq : m ^ 2 * massShellEnergy m (massShellBoost m A p) =
      m ^ 2 * (massShellEnergy m p * J.det) := by
    dsimp only [J, L'] at h_mat ⊢
    field_simp [hω1, hω2] at h_mat
    nlinarith
  have h_eq2 : massShellEnergy m (massShellBoost m A p) = massShellEnergy m p * J.det :=
    mul_left_cancel₀ hm2 h_eq
  rw [h_eq2, mul_div_cancel_left₀ _ hω1]

theorem abs_det_massShellBoostDerivCLM {m : ℝ} (hm : 0 < m) (A : SL2C)
    (p : Fin 3 → ℝ) :
    |(massShellBoostDerivCLM m A p).det| =
      massShellEnergy m (massShellBoost m A p) / massShellEnergy m p := by
  rw [det_massShellBoostDerivCLM hm A p]
  exact abs_of_pos (div_pos (massShellEnergy_pos hm _) (massShellEnergy_pos hm _))

theorem integral_massShell_lorentzOfSL2C_eq {m : ℝ} (hm : 0 < m) (A : SL2C)
    (F : (Fin 4 → ℝ) → ℂ) :
    (∫ p : Fin 3 → ℝ,
      ((2 * massShellEnergy m p)⁻¹ : ℂ) *
        F ((lorentzOfSL2C A).mulVec (massShellVec m p))) =
    ∫ p : Fin 3 → ℝ,
      ((2 * massShellEnergy m p)⁻¹ : ℂ) * F (massShellVec m p) := by
  let g : (Fin 3 → ℝ) → ℂ := fun q =>
    ((2 * massShellEnergy m q)⁻¹ : ℂ) * F (massShellVec m q)
  have h_jac := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
    (μ := volume) MeasurableSet.univ
    (fun p _ => (hasFDerivAt_massShellBoost hm A p).hasFDerivWithinAt)
    (massShellBoost_injOn hm A) g
  rw [massShellBoost_image_univ hm A, Measure.restrict_univ] at h_jac
  rw [h_jac]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  dsimp only [g]
  rw [abs_det_massShellBoostDerivCLM hm A p, Complex.real_smul,
      ← lorentzOfSL2C_mulVec_massShellVec hm A p]
  have hω1 : (massShellEnergy m p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (massShellEnergy_pos hm p).ne'
  have hω2 : (massShellEnergy m (massShellBoost m A p) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (massShellEnergy_pos hm (massShellBoost m A p)).ne'
  push_cast
  field_simp [hω1, hω2]

theorem integrable_massShellDecay :
    Integrable (fun p : Fin 3 → ℝ => ((1 + ‖p‖) ^ 4)⁻¹) volume := by
  have h := integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 4) (by simp; norm_num)
  refine h.congr (Filter.Eventually.of_forall (fun p => ?_))
  dsimp only
  have hp : 0 < 1 + ‖p‖ := by positivity
  rw [Real.rpow_neg hp.le]
  norm_cast

theorem integrable_exp_neg_massShellEnergy {m c : ℝ} (hm : 0 < m) (hc : 0 < c) :
    Integrable (fun p : Fin 3 → ℝ => Real.exp (-(c * massShellEnergy m p))) volume := by
  let K : ℝ := (1 / m + 1) / c
  have hK_pos : 0 < K := by dsimp [K]; positivity
  have h_meas : Measurable (fun p : Fin 3 → ℝ => Real.exp (-(c * massShellEnergy m p))) :=
    Real.continuous_exp.measurable.comp
      (measurable_neg.comp (measurable_const.mul (continuous_massShellEnergy m).measurable))
  refine Integrable.mono' (integrable_massShellDecay.const_mul (24 * K ^ 4))
    h_meas.aestronglyMeasurable (Filter.Eventually.of_forall (fun p => ?_))
  have hω_pos : 0 < massShellEnergy m p := massShellEnergy_pos hm p
  have hcω_nn : 0 ≤ c * massShellEnergy m p := mul_nonneg hc.le hω_pos.le
  have h_lin : 1 + ‖p‖ ≤ K * (c * massShellEnergy m p) := by
    have h1 := one_add_norm_le_scale_massShellEnergy hm p
    have hK_eq : K * (c * massShellEnergy m p) = (1 / m + 1) * massShellEnergy m p := by
      dsimp [K]
      field_simp [hc.ne']
    linarith
  have h_pow : (1 + ‖p‖) ^ 4 ≤ K ^ 4 * (c * massShellEnergy m p) ^ 4 := by
    calc (1 + ‖p‖) ^ 4
        ≤ (K * (c * massShellEnergy m p)) ^ 4 :=
          pow_le_pow_left₀ (by positivity) h_lin 4
      _ = K ^ 4 * (c * massShellEnergy m p) ^ 4 := mul_pow _ _ 4
  have h_exp_fac :
      (c * massShellEnergy m p) ^ 4 / (24 : ℝ) ≤ Real.exp (c * massShellEnergy m p) := by
    simpa [Nat.factorial] using Real.pow_div_factorial_le_exp (c * massShellEnergy m p) hcω_nn 4
  have h_prod :
      (1 + ‖p‖) ^ 4 * Real.exp (-(c * massShellEnergy m p)) ≤ 24 * K ^ 4 := by
    calc (1 + ‖p‖) ^ 4 * Real.exp (-(c * massShellEnergy m p))
        ≤ (K ^ 4 * (c * massShellEnergy m p) ^ 4) *
            Real.exp (-(c * massShellEnergy m p)) :=
          mul_le_mul_of_nonneg_right h_pow (Real.exp_pos _).le
      _ = (24 * K ^ 4) * (((c * massShellEnergy m p) ^ 4 / 24) *
            Real.exp (-(c * massShellEnergy m p))) := by ring
      _ ≤ (24 * K ^ 4) *
            (Real.exp (c * massShellEnergy m p) * Real.exp (-(c * massShellEnergy m p))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right h_exp_fac (Real.exp_pos _).le) (by positivity)
      _ = 24 * K ^ 4 := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  have h_pos4 : 0 < (1 + ‖p‖) ^ 4 := by positivity
  exact (le_mul_inv_iff₀' h_pos4).mpr h_prod

lemma one_add_norm_le_momentumToEuclid_massShell (m : ℝ) (p : Fin 3 → ℝ) :
    1 + ‖p‖ ≤
      (2 * Real.pi) *
        (1 + ‖momentumToEuclidCLMN 2 (twoPointMomentum (massShellVec m p))‖) := by
  let u := momentumToEuclidCLMN 2 (twoPointMomentum (massShellVec m p))
  have hpi : 0 < 2 * Real.pi := by positivity
  have hp_norm : ‖p‖ ≤ (2 * Real.pi) * ‖u‖ := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hpi.le (norm_nonneg u))).mpr (fun j => ?_)
    have hu_coord : u (0, j.succ) = (2 * Real.pi)⁻¹ * p j := by
      dsimp [u, momentumToEuclidCLMN, posScaledMomentumCLMN, posScaledMomentumN,
        piSpaceEquiv, finCurryEquiv, finEuclidEquiv, twoPointMomentum, massShellVec]
      fin_cases j <;> simp
    have hpj : p j = (2 * Real.pi) * u (0, j.succ) := by
      rw [hu_coord]
      field_simp [hpi.ne']
    calc ‖p j‖ = ‖(2 * Real.pi) * u (0, j.succ)‖ := by rw [hpj]
      _ = (2 * Real.pi) * ‖u (0, j.succ)‖ := by
          rw [norm_mul, Real.norm_of_nonneg hpi.le]
      _ ≤ (2 * Real.pi) * ‖u‖ :=
          mul_le_mul_of_nonneg_left (PiLp.norm_apply_le u (0, j.succ)) hpi.le
  have hpi1 : 1 ≤ 2 * Real.pi := by
    have := Real.pi_gt_three
    linarith
  linarith

theorem norm_schwartz_momentumToEuclid_massShell_le (m : ℝ)
    (g : SchwartzMap (EuclideanSpace ℝ (Fin 2 × Fin 4)) ℂ) (p : Fin 3 → ℝ) :
    ‖g (momentumToEuclidCLMN 2 (twoPointMomentum (massShellVec m p)))‖ ≤
      ((4 * Real.pi) ^ 4 *
        ((Finset.Iic (4, 0)).sup
          (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin 2 × Fin 4)) ℂ) g)) *
        ((1 + ‖p‖) ^ 4)⁻¹ := by
  let u := momentumToEuclidCLMN 2 (twoPointMomentum (massShellVec m p))
  let S : ℝ := (Finset.Iic (4, 0)).sup
    (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin 2 × Fin 4)) ℂ) g
  have h_sch : (1 + ‖u‖) ^ 4 * ‖g u‖ ≤ 2 ^ 4 * S := by
    have h0 := SchwartzMap.one_add_le_sup_seminorm_apply
      (𝕜 := ℂ) (m := (4, 0)) (k := 4) (n := 0) le_rfl le_rfl g u
    have h_fam :
        (fun m : ℕ × ℕ =>
          SchwartzMap.seminorm (E := EuclideanSpace ℝ (Fin 2 × Fin 4)) (F := ℂ) ℂ m.1 m.2) =
        schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin 2 × Fin 4)) ℂ := rfl
    simpa [norm_iteratedFDeriv_zero, h_fam, S] using h0
  have h_p : (1 + ‖p‖) ^ 4 ≤ (2 * Real.pi) ^ 4 * (1 + ‖u‖) ^ 4 := by
    calc (1 + ‖p‖) ^ 4
        ≤ ((2 * Real.pi) * (1 + ‖u‖)) ^ 4 :=
          pow_le_pow_left₀ (by positivity)
            (one_add_norm_le_momentumToEuclid_massShell m p) 4
      _ = (2 * Real.pi) ^ 4 * (1 + ‖u‖) ^ 4 := mul_pow _ _ 4
  have h_prod : (1 + ‖p‖) ^ 4 * ‖g u‖ ≤ (4 * Real.pi) ^ 4 * S := by
    calc (1 + ‖p‖) ^ 4 * ‖g u‖
        ≤ ((2 * Real.pi) ^ 4 * (1 + ‖u‖) ^ 4) * ‖g u‖ :=
          mul_le_mul_of_nonneg_right h_p (norm_nonneg _)
      _ = (2 * Real.pi) ^ 4 * ((1 + ‖u‖) ^ 4 * ‖g u‖) := by ring
      _ ≤ (2 * Real.pi) ^ 4 * (2 ^ 4 * S) :=
          mul_le_mul_of_nonneg_left h_sch (by positivity)
      _ = (4 * Real.pi) ^ 4 * S := by ring
  have h_pos4 : 0 < (1 + ‖p‖) ^ 4 := by positivity
  exact (le_mul_inv_iff₀' h_pos4).mpr h_prod

noncomputable def massShellWeight {κ : Type*} (m : ℝ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (α : Fin 2 → κ) (p : Fin 3 → ℝ) : ℂ :=
  ((2 * massShellEnergy m p)⁻¹ : ℂ) * C α (massShellVec m p)

def MassShellCoeffData {κ : Type*} (m : ℝ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) : Prop :=
  (∀ α : Fin 2 → κ, Measurable (fun p : Fin 3 → ℝ => C α (massShellVec m p))) ∧
  (∀ α : Fin 2 → κ, ∃ B : ℝ, 0 ≤ B ∧ ∀ p : Fin 3 → ℝ, ‖massShellWeight m C α p‖ ≤ B)

lemma measurable_massShellWeight {κ : Type*} {m : ℝ}
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C) (α : Fin 2 → κ) :
    Measurable (massShellWeight m C α) := by
  unfold massShellWeight
  have h_inv : Measurable (fun p : Fin 3 → ℝ => ((2 * massShellEnergy m p)⁻¹ : ℂ)) :=
    (measurable_const.mul
      (Complex.continuous_ofReal.measurable.comp (continuous_massShellEnergy m).measurable)).inv
  exact h_inv.mul (hC.1 α)

theorem integrable_massShellWeight_mul_schwartz {κ : Type*} {m : ℝ}
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C) (α : Fin 2 → κ)
    (g : SchwartzMap (EuclideanSpace ℝ (Fin 2 × Fin 4)) ℂ) :
    Integrable (fun p : Fin 3 → ℝ =>
      massShellWeight m C α p *
        g (momentumToEuclidCLMN 2 (twoPointMomentum (massShellVec m p)))) volume := by
  rcases hC.2 α with ⟨B, hB_nn, hB⟩
  let Kg : ℝ := (4 * Real.pi) ^ 4 *
    ((Finset.Iic (4, 0)).sup
      (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin 2 × Fin 4)) ℂ) g)
  have h_meas_two : Measurable (fun p : Fin 3 → ℝ => twoPointMomentum (massShellVec m p)) := by
    refine measurable_pi_lambda _ (fun i => ?_)
    fin_cases i
    · exact (continuous_massShellVec m).measurable
    · exact (continuous_massShellVec m).measurable.neg
  have h_meas_g : Measurable (fun p : Fin 3 → ℝ =>
      g (momentumToEuclidCLMN 2 (twoPointMomentum (massShellVec m p)))) :=
    (g.continuous.comp (momentumToEuclidCLMN 2).continuous).measurable.comp h_meas_two
  refine Integrable.mono' (integrable_massShellDecay.const_mul (B * Kg))
    ((measurable_massShellWeight hC α).mul h_meas_g).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => ?_))
  rw [norm_mul]
  calc ‖massShellWeight m C α p‖ *
        ‖g (momentumToEuclidCLMN 2 (twoPointMomentum (massShellVec m p)))‖
      ≤ B * (Kg * ((1 + ‖p‖) ^ 4)⁻¹) :=
        mul_le_mul (hB p) (norm_schwartz_momentumToEuclid_massShell_le m g p)
          (norm_nonneg _) hB_nn
    _ = (B * Kg) * ((1 + ‖p‖) ^ 4)⁻¹ := by ring

noncomputable def massShellEuclidCLM {κ : Type*} (m : ℝ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C) (α : Fin 2 → κ) :
    SchwartzMap (EuclideanSpace ℝ (Fin 2 × Fin 4)) ℂ →L[ℂ] ℂ :=
  SchwartzMap.mkCLMtoNormedSpace
    (fun g => ∫ p : Fin 3 → ℝ,
      massShellWeight m C α p *
        g (momentumToEuclidCLMN 2 (twoPointMomentum (massShellVec m p))))
    (fun g₁ g₂ => by
      have h_add :
          (fun p : Fin 3 → ℝ =>
            massShellWeight m C α p *
              (g₁ + g₂) (momentumToEuclidCLMN 2 (twoPointMomentum (massShellVec m p)))) =
          fun p : Fin 3 → ℝ =>
            massShellWeight m C α p *
              g₁ (momentumToEuclidCLMN 2 (twoPointMomentum (massShellVec m p))) +
            massShellWeight m C α p *
              g₂ (momentumToEuclidCLMN 2 (twoPointMomentum (massShellVec m p))) := by
        ext p
        simp [mul_add]
      rw [h_add]
      exact integral_add (integrable_massShellWeight_mul_schwartz hC α g₁)
        (integrable_massShellWeight_mul_schwartz hC α g₂))
    (fun c g => by
      have h_smul :
          (fun p : Fin 3 → ℝ =>
            massShellWeight m C α p *
              (c • g) (momentumToEuclidCLMN 2 (twoPointMomentum (massShellVec m p)))) =
          fun p : Fin 3 → ℝ =>
            c * (massShellWeight m C α p *
              g (momentumToEuclidCLMN 2 (twoPointMomentum (massShellVec m p)))) := by
        ext p
        simp [smul_eq_mul, mul_left_comm]
      rw [h_smul, RingHom.id_apply, smul_eq_mul, integral_const_mul])
    (by
      let B : ℝ := Classical.choose (hC.2 α)
      have hB_spec := Classical.choose_spec (hC.2 α)
      have hB_nn : 0 ≤ B := hB_spec.1
      have hB : ∀ p : Fin 3 → ℝ, ‖massShellWeight m C α p‖ ≤ B := hB_spec.2
      let I_dec : ℝ := ∫ p : Fin 3 → ℝ, ((1 + ‖p‖) ^ 4)⁻¹
      have hI_nn : 0 ≤ I_dec := integral_nonneg (fun p => by positivity)
      refine ⟨Finset.Iic (4, 0), B * (4 * Real.pi) ^ 4 * I_dec, by positivity, fun g => ?_⟩
      let S : ℝ := (Finset.Iic (4, 0)).sup
        (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin 2 × Fin 4)) ℂ) g
      calc ‖∫ p : Fin 3 → ℝ, massShellWeight m C α p *
              g (momentumToEuclidCLMN 2 (twoPointMomentum (massShellVec m p)))‖
          ≤ ∫ p : Fin 3 → ℝ,
              ‖massShellWeight m C α p *
                g (momentumToEuclidCLMN 2 (twoPointMomentum (massShellVec m p)))‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ p : Fin 3 → ℝ,
              (B * ((4 * Real.pi) ^ 4 * S)) * ((1 + ‖p‖) ^ 4)⁻¹ := by
            refine integral_mono_of_nonneg
              (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
              (integrable_massShellDecay.const_mul (B * ((4 * Real.pi) ^ 4 * S)))
              (Filter.Eventually.of_forall (fun p => ?_))
            dsimp only
            rw [norm_mul]
            calc ‖massShellWeight m C α p‖ *
                  ‖g (momentumToEuclidCLMN 2 (twoPointMomentum (massShellVec m p)))‖
                ≤ B * (((4 * Real.pi) ^ 4 * S) * ((1 + ‖p‖) ^ 4)⁻¹) :=
                  mul_le_mul (hB p) (norm_schwartz_momentumToEuclid_massShell_le m g p)
                    (norm_nonneg _) hB_nn
              _ = (B * ((4 * Real.pi) ^ 4 * S)) * ((1 + ‖p‖) ^ 4)⁻¹ := by ring
        _ = (B * (4 * Real.pi) ^ 4 * I_dec) * S := by
            rw [integral_const_mul]
            dsimp [I_dec]
            ring)

noncomputable def massShellTwoPointW {κ : Type*} (m : ℝ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C) :
    WightmanFamily κ
  | 0, α => vacW 0 α
  | 2, α =>
      PointwiseConvergenceCLM.precomp ℂ (minkowskiFourierSchwartzCLM 2)
        (ContinuousLinearMap.toPointwiseConvergenceCLM _ _ _ _
          (massShellEuclidCLM m C hC α))
  | 1, _ => 0
  | _ + 3, _ => 0

@[simp]
theorem massShellTwoPointW_zero_apply {κ : Type*} (m : ℝ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C)
    (α : Fin 0 → κ) (f : SchwartzMap (Fin 0 → Fin 4 → ℝ) ℂ) :
    massShellTwoPointW m C hC 0 α f = f 0 := rfl

@[simp]
theorem massShellTwoPointW_one_apply {κ : Type*} (m : ℝ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C)
    (α : Fin 1 → κ) (f : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    massShellTwoPointW m C hC 1 α f = 0 := rfl

@[simp]
theorem massShellTwoPointW_add_three_apply {κ : Type*} (m : ℝ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C)
    (k : ℕ) (α : Fin (k + 3) → κ) (f : SchwartzMap (Fin (k + 3) → Fin 4 → ℝ) ℂ) :
    massShellTwoPointW m C hC (k + 3) α f = 0 := rfl

@[simp]
theorem massShellTwoPointW_two_apply {κ : Type*} (m : ℝ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C)
    (α : Fin 2 → κ) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ) :
    massShellTwoPointW m C hC 2 α f =
      ∫ p : Fin 3 → ℝ, massShellWeight m C α p *
        minkowskiFourier f (twoPointMomentum (massShellVec m p)) := by
  change ∫ p : Fin 3 → ℝ, massShellWeight m C α p *
    (minkowskiFourierSchwartzCLM 2 f)
      (momentumToEuclidCLMN 2 (twoPointMomentum (massShellVec m p))) = _
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  dsimp only
  rw [← minkowskiFourier_eq_minkowskiFourierSchwartzCLM 2 f
    (twoPointMomentum (massShellVec m p))]

theorem integrable_massShellWeight_mul_minkowskiFourier {κ : Type*} {m : ℝ}
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C) (α : Fin 2 → κ)
    (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ) :
    Integrable (fun p : Fin 3 → ℝ =>
      massShellWeight m C α p *
        minkowskiFourier f (twoPointMomentum (massShellVec m p))) volume := by
  have h_eq :
      (fun p : Fin 3 → ℝ =>
        massShellWeight m C α p *
          minkowskiFourier f (twoPointMomentum (massShellVec m p))) =
      fun p : Fin 3 → ℝ =>
        massShellWeight m C α p *
          (minkowskiFourierSchwartzCLM 2 f)
            (momentumToEuclidCLMN 2 (twoPointMomentum (massShellVec m p))) := by
    ext p
    rw [minkowskiFourier_eq_minkowskiFourierSchwartzCLM 2 f]
  rw [h_eq]
  exact integrable_massShellWeight_mul_schwartz hC α (minkowskiFourierSchwartzCLM 2 f)

noncomputable def massShellTwoPointH {κ : Type*} (m : ℝ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) :
    ∀ n : ℕ, (Fin n → κ) → (Fin n → Fin 4 → ℂ) → ℂ
  | 0, _, _ => 1
  | 2, α, z =>
      ∫ p : Fin 3 → ℝ, massShellWeight m C α p *
        vladimirov_kernel 2 z (twoPointMomentum (massShellVec m p))
  | 1, _, _ => 0
  | _ + 3, _, _ => 0

@[simp]
lemma massShellTwoPointH_zero {κ : Type*} (m : ℝ) (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ)
    (α : Fin 0 → κ) (z : Fin 0 → Fin 4 → ℂ) :
    massShellTwoPointH m C 0 α z = 1 := rfl

@[simp]
lemma massShellTwoPointH_one {κ : Type*} (m : ℝ) (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ)
    (α : Fin 1 → κ) (z : Fin 1 → Fin 4 → ℂ) :
    massShellTwoPointH m C 1 α z = 0 := rfl

@[simp]
lemma massShellTwoPointH_add_three {κ : Type*} (m : ℝ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (k : ℕ)
    (α : Fin (k + 3) → κ) (z : Fin (k + 3) → Fin 4 → ℂ) :
    massShellTwoPointH m C (k + 3) α z = 0 := rfl

@[simp]
lemma massShellTwoPointH_two {κ : Type*} (m : ℝ) (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ)
    (α : Fin 2 → κ) (z : Fin 2 → Fin 4 → ℂ) :
    massShellTwoPointH m C 2 α z =
      ∫ p : Fin 3 → ℝ, massShellWeight m C α p *
        vladimirov_kernel 2 z (twoPointMomentum (massShellVec m p)) := rfl

noncomputable def zTwoShift (ε : ℝ) : Fin 2 → Fin 4 → ℂ :=
  fun i μ => if i = 1 ∧ μ = 0 then Complex.I * (ε : ℂ) else 0

lemma exp_mul_vladimirov_kernel_sub_zTwoShift (ε : ℝ) (q : Fin 4 → ℝ)
    (z : Fin 2 → Fin 4 → ℂ) :
    ((Real.exp (-(ε * q 0)) : ℝ) : ℂ) *
        vladimirov_kernel 2 (z - zTwoShift ε) (twoPointMomentum q) =
      vladimirov_kernel 2 z (twoPointMomentum q) := by
  unfold vladimirov_kernel
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [Fin.isValue, twoPointMomentum_zero, twoPointMomentum_one, Pi.sub_apply,
    Pi.neg_apply, Complex.ofReal_neg, zTwoShift, Fin.zero_ne_one, false_and, ↓reduceIte,
    sub_zero, true_and, Fin.reduceEq, minkowskiInnerC]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

noncomputable def dampedTwoPointMeasureFamily (m : ℝ) (hm : 0 < m)
    (ε : ℝ) (hε : 0 < ε) (w : (Fin 3 → ℝ) → ℂ) (hw_meas : Measurable w)
    (B : ℝ) (_hB_nn : 0 ≤ B) (hw_bound : ∀ p : Fin 3 → ℝ, ‖w p‖ ≤ B) :
    ForwardConeSpectralMeasureFamily Unit where
  A _ := Fin 3 → ℝ
  instMeas _ := inferInstance
  μ _ := volume
  instSFinite _ := inferInstance
  ρ
    | 2, _, p => w p * ((Real.exp (-(ε * massShellEnergy m p)) : ℝ) : ℂ)
    | 0, _, _ => 0
    | 1, _, _ => 0
    | _ + 3, _, _ => 0
  integrable_ρ
    | 2, _ => by
        have h_meas_exp : Measurable
            (fun p : Fin 3 → ℝ => ((Real.exp (-(ε * massShellEnergy m p)) : ℝ) : ℂ)) :=
          Complex.continuous_ofReal.measurable.comp
            (Real.continuous_exp.measurable.comp
              (measurable_neg.comp
                (measurable_const.mul (continuous_massShellEnergy m).measurable)))
        refine Integrable.mono'
          ((integrable_exp_neg_massShellEnergy hm hε).const_mul B)
          (hw_meas.mul h_meas_exp).aestronglyMeasurable
          (Filter.Eventually.of_forall (fun p => ?_))
        dsimp only
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
        exact mul_le_mul_of_nonneg_right (hw_bound p) (Real.exp_pos _).le
    | 0, _ => integrable_zero _ _ _
    | 1, _ => integrable_zero _ _ _
    | _ + 3, _ => integrable_zero _ _ _
  p
    | 2, _, q => twoPointMomentum (massShellVec m q)
    | 0, _, _ => 0
    | 1, _, _ => 0
    | _ + 3, _, _ => 0
  measurable_p
    | 2, _ => by
        refine measurable_pi_lambda _ (fun i => ?_)
        fin_cases i
        · exact (continuous_massShellVec m).measurable
        · exact (continuous_massShellVec m).measurable.neg
    | 0, _ => measurable_const
    | 1, _ => measurable_const
    | _ + 3, _ => measurable_const
  mem_forwardCone
    | 2, _, q =>
        twoPointMomentum_mem_forwardConeSpectralRegion
          (massShellVec_mem_closure_forward_light_cone hm q)
    | 0, _, _ => zero_mem_forwardConeSpectralRegion 0
    | 1, _, _ => zero_mem_forwardConeSpectralRegion 1
    | k + 3, _, _ => zero_mem_forwardConeSpectralRegion (k + 3)

theorem analyticOn_massShellTwoPointH {κ : Type*} {m : ℝ} (hm : 0 < m)
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (n : ℕ) (α : Fin n → κ) :
    AnalyticOn ℂ (massShellTwoPointH m C n α) (forward_tube_n n) := by
  match n with
  | 0 => exact analyticOn_const
  | 1 => exact analyticOn_const
  | k + 3 => exact analyticOn_const
  | 2 =>
      rw [(forward_tube_n_isOpen 2).analyticOn_iff_analyticOnNhd]
      intro z₀ hz₀
      have h_cont_shift : Continuous (fun ε : ℝ => z₀ - zTwoShift ε) := by
        refine continuous_const.sub (continuous_pi (fun i => continuous_pi (fun μ => ?_)))
        dsimp [zTwoShift]
        split_ifs
        · exact continuous_const.mul Complex.continuous_ofReal
        · exact continuous_const
      have h_open_eps : IsOpen ((fun ε : ℝ => z₀ - zTwoShift ε) ⁻¹' forward_tube_n 2) :=
        (forward_tube_n_isOpen 2).preimage h_cont_shift
      have h0_mem : (0 : ℝ) ∈ (fun ε : ℝ => z₀ - zTwoShift ε) ⁻¹' forward_tube_n 2 := by
        have h_z0 : z₀ - zTwoShift 0 = z₀ := by
          ext i μ
          simp [zTwoShift]
        change z₀ - zTwoShift 0 ∈ forward_tube_n 2
        rwa [h_z0]
      rcases Metric.isOpen_iff.mp h_open_eps 0 h0_mem with ⟨δ, hδ_pos, hδ_sub⟩
      let ε : ℝ := δ / 2
      have hε_pos : 0 < ε := half_pos hδ_pos
      have hz_shift : z₀ - zTwoShift ε ∈ forward_tube_n 2 := by
        apply hδ_sub
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hε_pos]
        exact half_lt_self hδ_pos
      rcases hC.2 α with ⟨B, hB_nn, hB⟩
      let F_damp := dampedTwoPointMeasureFamily m hm ε hε_pos
        (massShellWeight m C α) (measurable_massShellWeight hC α) B hB_nn hB
      have h_eq : massShellTwoPointH m C 2 α =
          fun z => F_damp.H 2 default (z - zTwoShift ε) := by
        ext z
        unfold massShellTwoPointH ForwardConeSpectralMeasureFamily.H
        refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        dsimp [F_damp, dampedTwoPointMeasureFamily]
        have hω0 : massShellEnergy m p = massShellVec m p 0 := rfl
        rw [mul_assoc, hω0,
            exp_mul_vladimirov_kernel_sub_zTwoShift ε (massShellVec m p) z]
      rw [h_eq]
      exact (F_damp.analyticAt_H 2 default hz_shift).comp_of_eq
        (analyticAt_id.sub analyticAt_const) rfl

lemma norm_vladimirov_kernel_twoPoint_le_exp {m : ℝ} (hm : 0 < m)
    {z : Fin 2 → Fin 4 → ℂ} (_hz : z ∈ forward_tube_n 2) (p : Fin 3 → ℝ) :
    ‖vladimirov_kernel 2 z (twoPointMomentum (massShellVec m p))‖ ≤
      Real.exp (-(coneGap (diff_im 2 z 0 (by decide)) * massShellEnergy m p)) := by
  have hp_cone := twoPointMomentum_mem_forwardConeSpectralRegion
    (massShellVec_mem_closure_forward_light_cone hm p)
  rw [vladimirov_kernel_norm, sum_minkowskiInner_im_eq_neg_totalConePairing 2 _ z hp_cone.1]
  have h_pair : totalConePairing 2 (twoPointMomentum (massShellVec m p)) z =
      minkowskiInner (massShellVec m p) (diff_im 2 z 0 (by decide)) := by
    unfold totalConePairing
    rw [Fin.sum_univ_two]
    dsimp [partial_sum_p]
    rw [partial_sum_twoPointMomentum]
    simp
  have h_ge : coneGap (diff_im 2 z 0 (by decide)) * massShellEnergy m p ≤
      minkowskiInner (massShellVec m p) (diff_im 2 z 0 (by decide)) :=
    minkowskiInner_ge_coneGap_closure (diff_im 2 z 0 (by decide)) (massShellVec m p)
      (massShellVec_mem_closure_forward_light_cone hm p)
  rw [h_pair]
  exact Real.exp_le_exp.mpr (by linarith)

theorem integrable_massShellWeight_mul_kernel {κ : Type*} {m : ℝ} (hm : 0 < m)
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (α : Fin 2 → κ) {z : Fin 2 → Fin 4 → ℂ} (hz : z ∈ forward_tube_n 2) :
    Integrable (fun p : Fin 3 → ℝ =>
      massShellWeight m C α p *
        vladimirov_kernel 2 z (twoPointMomentum (massShellVec m p))) volume := by
  rcases hC.2 α with ⟨B, hB_nn, hB⟩
  let c₀ : ℝ := coneGap (diff_im 2 z 0 (by decide))
  have hc₀ : 0 < c₀ := coneGap_pos _ (diff_im_mem_forward_cone 2 z hz 0 (by decide))
  have h_meas_two : Measurable (fun p : Fin 3 → ℝ => twoPointMomentum (massShellVec m p)) := by
    refine measurable_pi_lambda _ (fun i => ?_)
    fin_cases i
    · exact (continuous_massShellVec m).measurable
    · exact (continuous_massShellVec m).measurable.neg
  have h_meas_ker : Measurable (fun p : Fin 3 → ℝ =>
      vladimirov_kernel 2 z (twoPointMomentum (massShellVec m p))) :=
    (vladimirov_kernel_contDiff 2 z).continuous.measurable.comp h_meas_two
  refine Integrable.mono' ((integrable_exp_neg_massShellEnergy hm hc₀).const_mul B)
    ((measurable_massShellWeight hC α).mul h_meas_ker).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => ?_))
  rw [norm_mul]
  exact mul_le_mul (hB p) (norm_vladimirov_kernel_twoPoint_le_exp hm hz p)
    (norm_nonneg _) hB_nn

lemma integrable_prod_massShellWeight_line_mul_f {κ : Type*} {m : ℝ} (hm : 0 < m)
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (α : Fin 2 → κ) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ)
    {v : Fin 4 → ℝ} (hv : v ∈ forward_light_cone) {t : ℝ} (ht : 0 < t) :
    Integrable
      (Function.uncurry (fun (p : Fin 3 → ℝ) (x : Fin 2 → Fin 4 → ℝ) =>
        massShellWeight m C α p *
          (vladimirov_kernel 2 (tubeBoundaryLine 2 x v t)
            (twoPointMomentum (massShellVec m p)) * f x)))
      (volume.prod volume) := by
  rcases hC.2 α with ⟨B, hB_nn, hB⟩
  let c₀ : ℝ := t * coneGap v
  have hc₀ : 0 < c₀ := mul_pos ht (coneGap_pos v hv)
  have h_dom : Integrable
      (fun px : (Fin 3 → ℝ) × (Fin 2 → Fin 4 → ℝ) =>
        (B * Real.exp (-(c₀ * massShellEnergy m px.1))) * ‖f px.2‖)
      (volume.prod volume) :=
    ((integrable_exp_neg_massShellEnergy hm hc₀).const_mul B).mul_prod f.integrable.norm
  have h_meas_two : Measurable (fun p : Fin 3 → ℝ => twoPointMomentum (massShellVec m p)) := by
    refine measurable_pi_lambda _ (fun i => ?_)
    fin_cases i
    · exact (continuous_massShellVec m).measurable
    · exact (continuous_massShellVec m).measurable.neg
  have h_meas_ker : Measurable
      (fun px : (Fin 3 → ℝ) × (Fin 2 → Fin 4 → ℝ) =>
        vladimirov_kernel 2 (tubeBoundaryLine 2 px.2 v t)
          (twoPointMomentum (massShellVec m px.1))) := by
    have h_phase : Measurable
        (fun px : (Fin 3 → ℝ) × (Fin 2 → Fin 4 → ℝ) =>
          -Complex.I * ∑ k : Fin 2,
            minkowskiInnerC
              (fun μ => (twoPointMomentum (massShellVec m px.1) k μ : ℂ))
              (tubeBoundaryLine 2 px.2 v t k)) := by
      refine measurable_const.mul (Finset.measurable_sum Finset.univ (fun k _ => ?_))
      have hk1 : Measurable
          (fun px : (Fin 3 → ℝ) × (Fin 2 → Fin 4 → ℝ) =>
            twoPointMomentum (massShellVec m px.1) k) :=
        (measurable_pi_apply k).comp (h_meas_two.comp measurable_fst)
      have hk2 : Measurable
          (fun px : (Fin 3 → ℝ) × (Fin 2 → Fin 4 → ℝ) => px.2 k) :=
        (measurable_pi_apply k).comp measurable_snd
      have hm1 : ∀ μ : Fin 4, Measurable
          (fun px : (Fin 3 → ℝ) × (Fin 2 → Fin 4 → ℝ) =>
            (twoPointMomentum (massShellVec m px.1) k μ : ℂ)) :=
        fun μ => Complex.continuous_ofReal.measurable.comp
          ((measurable_pi_apply μ).comp hk1)
      have hm2 : ∀ μ : Fin 4, Measurable
          (fun px : (Fin 3 → ℝ) × (Fin 2 → Fin 4 → ℝ) =>
            tubeBoundaryLine 2 px.2 v t k μ) :=
        fun μ => (Complex.continuous_ofReal.measurable.comp
          ((measurable_pi_apply μ).comp hk2)).add measurable_const
      exact (((hm1 0).mul (hm2 0)).sub ((hm1 1).mul (hm2 1))).sub
        ((hm1 2).mul (hm2 2)) |>.sub ((hm1 3).mul (hm2 3))
    exact Complex.continuous_exp.measurable.comp h_phase
  have h_meas : AEStronglyMeasurable
      (fun px : (Fin 3 → ℝ) × (Fin 2 → Fin 4 → ℝ) =>
        massShellWeight m C α px.1 *
          (vladimirov_kernel 2 (tubeBoundaryLine 2 px.2 v t)
            (twoPointMomentum (massShellVec m px.1)) * f px.2))
      (volume.prod volume) :=
    (((measurable_massShellWeight hC α).comp measurable_fst).aestronglyMeasurable).mul
      (h_meas_ker.aestronglyMeasurable.mul f.integrable.aestronglyMeasurable.comp_snd)
  have h_uncurry :
      Function.uncurry (fun (p : Fin 3 → ℝ) (x : Fin 2 → Fin 4 → ℝ) =>
        massShellWeight m C α p *
          (vladimirov_kernel 2 (tubeBoundaryLine 2 x v t)
            (twoPointMomentum (massShellVec m p)) * f x)) =
      fun px : (Fin 3 → ℝ) × (Fin 2 → Fin 4 → ℝ) =>
        massShellWeight m C α px.1 *
          (vladimirov_kernel 2 (tubeBoundaryLine 2 px.2 v t)
            (twoPointMomentum (massShellVec m px.1)) * f px.2) := rfl
  rw [h_uncurry]
  refine Integrable.mono' h_dom h_meas (Filter.Eventually.of_forall (fun px => ?_))
  rw [norm_mul, norm_mul]
  have hz_mem : tubeBoundaryLine 2 px.2 v t ∈ forward_tube_n 2 :=
    line_mem_forward_tube 2 px.2 v hv t ht
  have h_diff_im : diff_im 2 (tubeBoundaryLine 2 px.2 v t) 0 (by decide) = t • v := by
    ext μ
    simp [diff_im, diff_z, tubeBoundaryLine]
  have h_gap_t : coneGap (diff_im 2 (tubeBoundaryLine 2 px.2 v t) 0 (by decide)) = c₀ := by
    rw [h_diff_im]
    dsimp [c₀, coneGap]
    have h_sq : ((t * v 1) ^ 2 + (t * v 2) ^ 2 + (t * v 3) ^ 2) =
        t ^ 2 * ((v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2) := by ring
    rw [h_sq, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]
    ring
  have h_ker_le :
      ‖vladimirov_kernel 2 (tubeBoundaryLine 2 px.2 v t)
        (twoPointMomentum (massShellVec m px.1))‖ ≤
        Real.exp (-(c₀ * massShellEnergy m px.1)) := by
    simpa [h_gap_t] using norm_vladimirov_kernel_twoPoint_le_exp hm hz_mem px.1
  calc ‖massShellWeight m C α px.1‖ *
        (‖vladimirov_kernel 2 (tubeBoundaryLine 2 px.2 v t)
          (twoPointMomentum (massShellVec m px.1))‖ * ‖f px.2‖)
      ≤ B * (Real.exp (-(c₀ * massShellEnergy m px.1)) * ‖f px.2‖) :=
        mul_le_mul (hB px.1)
          (mul_le_mul_of_nonneg_right h_ker_le (norm_nonneg (f px.2)))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hB_nn
    _ = (B * Real.exp (-(c₀ * massShellEnergy m px.1))) * ‖f px.2‖ := by ring

theorem tendsto_massShellTwoPointH_boundary {κ : Type*} {m : ℝ} (hm : 0 < m)
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (n : ℕ) (α : Fin n → κ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    {v : Fin 4 → ℝ} (hv : v ∈ forward_light_cone) :
    Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        massShellTwoPointH m C n α (tubeBoundaryLine n x v t) * f x)
      (𝓝[>] 0)
      (𝓝 (massShellTwoPointW m C hC n α f)) := by
  match n with
  | 0 =>
      have h_eq : (fun t : ℝ => ∫ x : Fin 0 → Fin 4 → ℝ,
          massShellTwoPointH m C 0 α (tubeBoundaryLine 0 x v t) * f x) =
          fun _ => f 0 := by
        ext t
        simp [massShellTwoPointH_zero]
      rw [h_eq, massShellTwoPointW_zero_apply]
      exact tendsto_const_nhds
  | 1 =>
      have h_eq : (fun t : ℝ => ∫ x : Fin 1 → Fin 4 → ℝ,
          massShellTwoPointH m C 1 α (tubeBoundaryLine 1 x v t) * f x) =
          fun _ => 0 := by
        ext t
        simp [massShellTwoPointH_one]
      rw [h_eq, massShellTwoPointW_one_apply]
      exact tendsto_const_nhds
  | k + 3 =>
      have h_eq : (fun t : ℝ => ∫ x : Fin (k + 3) → Fin 4 → ℝ,
          massShellTwoPointH m C (k + 3) α (tubeBoundaryLine (k + 3) x v t) * f x) =
          fun _ => 0 := by
        ext t
        simp [massShellTwoPointH_add_three]
      rw [h_eq, massShellTwoPointW_add_three_apply]
      exact tendsto_const_nhds
  | 2 =>
      rcases hC.2 α with ⟨B, hB_nn, hB⟩
      let g_hat := minkowskiFourierSchwartzCLM 2 f
      let Kf : ℝ := (4 * Real.pi) ^ 4 *
        ((Finset.Iic (4, 0)).sup
          (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin 2 × Fin 4)) ℂ) g_hat)
      let G : ℝ → (Fin 3 → ℝ) → ℂ := fun t p =>
        massShellWeight m C α p *
          (Complex.exp (t * ∑ k : Fin 2, ((k : ℕ) : ℝ) *
            minkowskiInner (twoPointMomentum (massShellVec m p) k) v : ℂ) *
            minkowskiFourier f (twoPointMomentum (massShellVec m p)))
      have h_ev :
          (fun t : ℝ => ∫ x : Fin 2 → Fin 4 → ℝ,
            massShellTwoPointH m C 2 α (tubeBoundaryLine 2 x v t) * f x) =ᶠ[𝓝[>] 0]
          fun t : ℝ => ∫ p : Fin 3 → ℝ, G t p := by
        filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
        have h_lhs :
            (fun x : Fin 2 → Fin 4 → ℝ =>
              massShellTwoPointH m C 2 α (tubeBoundaryLine 2 x v t) * f x) =
            fun x : Fin 2 → Fin 4 → ℝ =>
              ∫ p : Fin 3 → ℝ, massShellWeight m C α p *
                (vladimirov_kernel 2 (tubeBoundaryLine 2 x v t)
                  (twoPointMomentum (massShellVec m p)) * f x) := by
          ext x
          rw [massShellTwoPointH_two, ← integral_mul_const]
          exact integral_congr_ae (Filter.Eventually.of_forall (fun _ => mul_assoc _ _ _))
        rw [h_lhs,
            (MeasureTheory.integral_integral_swap
              (integrable_prod_massShellWeight_line_mul_f hm hC α f hv ht)).symm]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        dsimp [G]
        rw [integral_const_mul,
            integral_vladimirov_kernel_line_mul_f 2 f
              (twoPointMomentum (massShellVec m p)) v t]
      rw [tendsto_congr' h_ev, massShellTwoPointW_two_apply]
      have h_meas_two : Measurable (fun p : Fin 3 → ℝ => twoPointMomentum (massShellVec m p)) := by
        refine measurable_pi_lambda _ (fun i => ?_)
        fin_cases i
        · exact (continuous_massShellVec m).measurable
        · exact (continuous_massShellVec m).measurable.neg
      refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (fun p => (B * Kf) * ((1 + ‖p‖) ^ 4)⁻¹) ?_ ?_
        (integrable_massShellDecay.const_mul (B * Kf)) ?_
      · refine Filter.Eventually.of_forall (fun t => ?_)
        have h_cont_q : Continuous (fun q : Fin 2 → Fin 4 → ℝ =>
            Complex.exp (t * ∑ k : Fin 2, ((k : ℕ) : ℝ) * minkowskiInner (q k) v : ℂ) *
              minkowskiFourier f q) := by
          have h_lin : Continuous (fun q : Fin 2 → Fin 4 → ℝ =>
              (t * ∑ k : Fin 2, ((k : ℕ) : ℝ) * minkowskiInner (q k) v : ℂ)) := by
            have h_real : Continuous (fun q : Fin 2 → Fin 4 → ℝ =>
                t * ∑ k : Fin 2, ((k : ℕ) : ℝ) * minkowskiInner (q k) v) := by
              refine continuous_const.mul (continuous_finsetSum Finset.univ (fun k _ => ?_))
              refine continuous_const.mul ?_
              simp only [minkowskiInner_explicit]
              have hc : ∀ μ : Fin 4, Continuous (fun q : Fin 2 → Fin 4 → ℝ => q k μ) :=
                fun μ => (continuous_apply μ).comp (continuous_apply k)
              exact (((hc 0).mul continuous_const).sub ((hc 1).mul continuous_const)).sub
                ((hc 2).mul continuous_const) |>.sub ((hc 3).mul continuous_const)
            have h_eq_c : (fun q : Fin 2 → Fin 4 → ℝ =>
                (t * ∑ k : Fin 2, ((k : ℕ) : ℝ) * minkowskiInner (q k) v : ℂ)) =
                fun q => ((t * ∑ k : Fin 2, ((k : ℕ) : ℝ) *
                  minkowskiInner (q k) v : ℝ) : ℂ) := by
              ext q
              push_cast
              rfl
            rw [h_eq_c]
            exact Complex.continuous_ofReal.comp h_real
          exact (Complex.continuous_exp.comp h_lin).mul (continuous_minkowskiFourier 2 f)
        exact ((measurable_massShellWeight hC α).mul
          (h_cont_q.measurable.comp h_meas_two)).aestronglyMeasurable
      · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
        refine Filter.Eventually.of_forall (fun p => ?_)
        dsimp [G]
        rw [norm_mul, norm_mul]
        have hp_cone := twoPointMomentum_mem_forwardConeSpectralRegion
          (massShellVec_mem_closure_forward_light_cone hm p)
        have h_exp_le :
            ‖Complex.exp (t * ∑ k : Fin 2, ((k : ℕ) : ℝ) *
              minkowskiInner (twoPointMomentum (massShellVec m p) k) v : ℂ)‖ ≤ 1 := by
          have h_cast :
              (t * ∑ k : Fin 2, ((k : ℕ) : ℝ) *
                minkowskiInner (twoPointMomentum (massShellVec m p) k) v : ℂ) =
              ((t * ∑ k : Fin 2, ((k : ℕ) : ℝ) *
                minkowskiInner (twoPointMomentum (massShellVec m p) k) v : ℝ) : ℂ) := by
            push_cast
            rfl
          rw [h_cast, Complex.norm_exp_ofReal]
          exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ht.le
            (sum_k_minkowskiInner_le_zero_of_forwardConeSpectralRegion 2 hp_cone hv))
        have h_four_le :
            ‖minkowskiFourier f (twoPointMomentum (massShellVec m p))‖ ≤
              Kf * ((1 + ‖p‖) ^ 4)⁻¹ := by
          rw [minkowskiFourier_eq_minkowskiFourierSchwartzCLM 2 f]
          exact norm_schwartz_momentumToEuclid_massShell_le m g_hat p
        calc ‖massShellWeight m C α p‖ *
              (‖Complex.exp (t * ∑ k : Fin 2, ((k : ℕ) : ℝ) *
                minkowskiInner (twoPointMomentum (massShellVec m p) k) v : ℂ)‖ *
                ‖minkowskiFourier f (twoPointMomentum (massShellVec m p))‖)
            ≤ B * (Kf * ((1 + ‖p‖) ^ 4)⁻¹) :=
              mul_le_mul (hB p)
                ((mul_le_of_le_one_left (norm_nonneg _) h_exp_le).trans h_four_le)
                (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hB_nn
          _ = (B * Kf) * ((1 + ‖p‖) ^ 4)⁻¹ := by ring
      · refine Filter.Eventually.of_forall (fun p => ?_)
        have h_cont_t : Continuous (fun t : ℝ => G t p) :=
          continuous_const.mul
            ((Complex.continuous_exp.comp
              (Complex.continuous_ofReal.mul continuous_const)).mul continuous_const)
        have h0 : G 0 p = massShellWeight m C α p *
            minkowskiFourier f (twoPointMomentum (massShellVec m p)) := by
          dsimp [G]
          simp
        rw [← h0]
        exact (h_cont_t.tendsto 0).mono_left nhdsWithin_le_nhds

noncomputable def massShellTwoPointTubeExtension {κ : Type*} (m : ℝ) (hm : 0 < m)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C) :
    TubeExtension (massShellTwoPointW m C hC) where
  H := massShellTwoPointH m C
  analytic n α := analyticOn_massShellTwoPointH hm hC n α
  boundary n α f _v hv := tendsto_massShellTwoPointH_boundary hm hC n α f hv

@[simp]
theorem massShellTwoPointTubeExtension_H {κ : Type*} (m : ℝ) (hm : 0 < m)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C) :
    (massShellTwoPointTubeExtension m hm C hC).H = massShellTwoPointH m C := rfl

noncomputable def massShellTwoPointS {κ : Type*} (m : ℝ) (hm : 0 < m)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C) :
    SchwingerFamily κ :=
  schwingerFromTube (massShellTwoPointTubeExtension m hm C hC)

@[simp]
theorem massShellTwoPointS_vacuumNormalized {κ : Type*} (m : ℝ) (hm : 0 < m)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C) :
    OSVacuumNormalized (massShellTwoPointS m hm C hC) := rfl

theorem massShellTwoPoint_forwardConeSpectrumCondition {κ : Type*} {m : ℝ} (hm : 0 < m)
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C) :
    ForwardConeSpectrumCondition (massShellTwoPointW m C hC) := by
  intro n α f ⟨U, _hU_open, hU_sub, hU_zero⟩
  match n with
  | 0 =>
      have h0 : minkowskiFourier f 0 = 0 :=
        hU_zero 0 (hU_sub (zero_mem_forwardConeSpectralRegion 0))
      rw [minkowskiFourier_eval_zero_n, integral_fin0] at h0
      rw [massShellTwoPointW_zero_apply, h0]
  | 1 => rfl
  | _ + 3 => rfl
  | 2 =>
      rw [massShellTwoPointW_two_apply]
      have h_zero : (fun p : Fin 3 → ℝ =>
          massShellWeight m C α p *
            minkowskiFourier f (twoPointMomentum (massShellVec m p))) = fun _ => 0 := by
        ext p
        have hp_cone := twoPointMomentum_mem_forwardConeSpectralRegion
          (massShellVec_mem_closure_forward_light_cone hm p)
        rw [hU_zero _ (hU_sub hp_cone), mul_zero]
      rw [h_zero, integral_zero]

omit [Fintype ι] [DecidableEq ι] in
theorem massShellTwoPointTubeTranslationInvariant {m : ℝ} (hm : 0 < m)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C) :
    TubeTranslationInvariant (massShellTwoPointTubeExtension m hm C hC) := by
  intro n α z a _hz
  match n with
  | 0 => rfl
  | 1 => rfl
  | _ + 3 => rfl
  | 2 =>
      change massShellTwoPointH m C 2 α (fun i => z i + a) = massShellTwoPointH m C 2 α z
      unfold massShellTwoPointH
      refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      dsimp only
      rw [vladimirov_kernel_add_const_of_sum_eq_zero 2
        (sum_twoPointMomentum (massShellVec m p)) z a]

omit [Fintype ι] [DecidableEq ι] in
theorem massShellTwoPointOSTranslationInvariant {m : ℝ} (hm : 0 < m)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C) :
    OSTranslationInvariant (massShellTwoPointS m hm C hC) :=
  schwingerFromTube_translation_invariant
    (massShellTwoPointTubeExtension m hm C hC)
    (massShellTwoPointTubeTranslationInvariant hm hC)

lemma twoPointMomentum_lorentzOfSL2C (A : SL2C) (q : Fin 4 → ℝ) :
    (fun k : Fin 2 => (lorentzOfSL2C A).mulVec (twoPointMomentum q k)) =
      twoPointMomentum ((lorentzOfSL2C A).mulVec q) := by
  ext k μ
  fin_cases k
  · rfl
  · simp [twoPointMomentum, Matrix.mulVec_neg]

theorem massShellTwoPointTubeCovariant (R : HolomorphicLorentzRep ι)
    {m : ℝ} (hm : 0 < m) {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R.rep A (α i) (β i)) * C β q) :
    TubeCovariant R (massShellTwoPointTubeExtension m hm C hC) := by
  intro n A z hz _hAz α
  match n with
  | 0 =>
      have hα : α = Fin.elim0 := Subsingleton.elim _ _
      subst hα
      simp [massShellTwoPointTubeExtension_H]
  | 1 =>
      simp [massShellTwoPointTubeExtension_H]
  | _ + 3 =>
      simp [massShellTwoPointTubeExtension_H]
  | 2 =>
      change massShellTwoPointH m C 2 α (spinorPhi (A, sl2c_conj A) • z) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R.rep A (α i) (β i)) *
          massShellTwoPointH m C 2 β z
      rw [massShellTwoPointH_two]
      have h_ker : ∀ p : Fin 3 → ℝ,
          vladimirov_kernel 2 (spinorPhi (A, sl2c_conj A) • z)
            (twoPointMomentum (massShellVec m p)) =
          vladimirov_kernel 2 z
            (twoPointMomentum ((lorentzOfSL2C A⁻¹).mulVec (massShellVec m p))) := by
        intro p
        rw [vladimirov_kernel_lorentz_inv 2 A z (twoPointMomentum (massShellVec m p)),
            twoPointMomentum_lorentzOfSL2C A⁻¹ (massShellVec m p)]
      have h_lhs :
          (∫ p : Fin 3 → ℝ, massShellWeight m C α p *
            vladimirov_kernel 2 (spinorPhi (A, sl2c_conj A) • z)
              (twoPointMomentum (massShellVec m p))) =
          ∫ p : Fin 3 → ℝ, ((2 * massShellEnergy m p)⁻¹ : ℂ) *
            (C α (massShellVec m p) *
              vladimirov_kernel 2 z
                (twoPointMomentum ((lorentzOfSL2C A⁻¹).mulVec (massShellVec m p)))) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        dsimp [massShellWeight]
        rw [h_ker p, mul_assoc]
      rw [h_lhs,
          ← integral_massShell_lorentzOfSL2C_eq hm A
            (fun q => C α q *
              vladimirov_kernel 2 z (twoPointMomentum ((lorentzOfSL2C A⁻¹).mulVec q)))]
      have h_cancel : ∀ p : Fin 3 → ℝ,
          (lorentzOfSL2C A⁻¹).mulVec ((lorentzOfSL2C A).mulVec (massShellVec m p)) =
            massShellVec m p := by
        intro p
        rw [Matrix.mulVec_mulVec, ← lorentzOfSL2C_mul, inv_mul_cancel,
            lorentzOfSL2C_one, Matrix.one_mulVec]
      have h_sum_int :
          (∫ p : Fin 3 → ℝ, ((2 * massShellEnergy m p)⁻¹ : ℂ) *
            (C α ((lorentzOfSL2C A).mulVec (massShellVec m p)) *
              vladimirov_kernel 2 z
                (twoPointMomentum
                  ((lorentzOfSL2C A⁻¹).mulVec
                    ((lorentzOfSL2C A).mulVec (massShellVec m p)))))) =
          ∫ p : Fin 3 → ℝ, ∑ β : Fin 2 → ι,
            (∏ i : Fin 2, R.rep A (α i) (β i)) *
              (massShellWeight m C β p *
                vladimirov_kernel 2 z (twoPointMomentum (massShellVec m p))) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        dsimp only
        rw [h_cancel p, hC_cov A (massShellVec m p) α, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun β _ => ?_)
        dsimp [massShellWeight]
        ring
      rw [h_sum_int, integral_finsetSum Finset.univ (fun β _ =>
        (integrable_massShellWeight_mul_kernel hm hC β hz).const_mul _)]
      refine Finset.sum_congr rfl (fun β _ => ?_)
      rw [integral_const_mul, massShellTwoPointH_two]

theorem massShellTwoPointPoincareCovariant (R : HolomorphicLorentzRep ι)
    {m : ℝ} (hm : 0 < m) {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R.rep A (α i) (β i)) * C β q) :
    PoincareCovariant R (massShellTwoPointW m C hC) :=
  poincareCovariant_of_tubeCovariant_general R (massShellTwoPointW m C hC)
    (massShellTwoPointTubeExtension m hm C hC)
    (massShellTwoPointTubeCovariant R hm hC hC_cov)
    (massShellTwoPointTubeTranslationInvariant hm hC)

lemma star_vladimirov_kernel_twoPointMomentum (q : Fin 4 → ℝ) (z : Fin 2 → Fin 4 → ℂ) :
    star (vladimirov_kernel 2 z (twoPointMomentum q)) =
      vladimirov_kernel 2 (fun i μ => star (z (Fin.rev i) μ)) (twoPointMomentum q) := by
  unfold vladimirov_kernel
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  have h0 : Fin.rev (0 : Fin 2) = 1 := rfl
  have h1 : Fin.rev (1 : Fin 2) = 0 := rfl
  simp only [Fin.isValue, twoPointMomentum_zero, twoPointMomentum_one, Pi.neg_apply,
    Complex.ofReal_neg, h0, h1, minkowskiInnerC, map_mul, map_neg, map_add, map_sub,
    Complex.conj_I, Complex.conj_ofReal]
  ring

lemma vladimirov_kernel_neg_rev_twoPointMomentum (q : Fin 4 → ℝ) (z : Fin 2 → Fin 4 → ℂ) :
    vladimirov_kernel 2 (-(z ∘ Fin.rev)) (twoPointMomentum q) =
      vladimirov_kernel 2 z (twoPointMomentum q) := by
  unfold vladimirov_kernel
  congr 1
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  have h0 : Fin.rev (0 : Fin 2) = 1 := rfl
  have h1 : Fin.rev (1 : Fin 2) = 0 := rfl
  simp only [Fin.isValue, twoPointMomentum_zero, twoPointMomentum_one, Pi.neg_apply,
    Function.comp_apply, Complex.ofReal_neg, h0, h1, minkowskiInnerC]
  ring

theorem massShellTwoPointTubeWickHermiticity {R : HolomorphicLorentzRep ι}
    (S : StarStructure R) {m : ℝ} (hm : 0 < m)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q) :
    TubeWickHermiticity S (massShellTwoPointTubeExtension m hm C hC) := by
  intro n α z _hz hz_rev
  match n with
  | 0 =>
      have hα : α = Fin.elim0 := Subsingleton.elim _ _
      subst hα
      simp [massShellTwoPointTubeExtension_H]
  | 1 =>
      simp [massShellTwoPointTubeExtension_H]
  | _ + 3 =>
      simp [massShellTwoPointTubeExtension_H]
  | 2 =>
      let z_rev : Fin 2 → Fin 4 → ℂ := fun i μ => star (z (Fin.rev i) μ)
      change star (massShellTwoPointH m C 2 α z) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) *
          massShellTwoPointH m C 2 (β ∘ Fin.rev) z_rev
      rw [massShellTwoPointH_two, Complex.star_def, ← integral_conj]
      have h_int_eq :
          (∫ p : Fin 3 → ℝ, (starRingEnd ℂ)
            (massShellWeight m C α p *
              vladimirov_kernel 2 z (twoPointMomentum (massShellVec m p)))) =
          ∫ p : Fin 3 → ℝ, ∑ β : Fin 2 → ι,
            (∏ i : Fin 2, S.C (α i) (β i)) *
              (massShellWeight m C (β ∘ Fin.rev) p *
                vladimirov_kernel 2 z_rev (twoPointMomentum (massShellVec m p))) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        dsimp only
        have h_ker : (starRingEnd ℂ)
            (vladimirov_kernel 2 z (twoPointMomentum (massShellVec m p))) =
            vladimirov_kernel 2 z_rev (twoPointMomentum (massShellVec m p)) :=
          star_vladimirov_kernel_twoPointMomentum _ _
        have h_wt : (starRingEnd ℂ) (massShellWeight m C α p) =
            (2 * (massShellEnergy m p : ℂ))⁻¹ *
              ∑ β : Fin 2 → ι,
                (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) (massShellVec m p) := by
          unfold massShellWeight
          rw [map_mul, map_inv₀, map_mul, map_ofNat, Complex.conj_ofReal,
              ← Complex.star_def, hC_herm (massShellVec m p) α]
        rw [map_mul, h_ker, h_wt, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun β _ => ?_)
        unfold massShellWeight
        ring
      rw [h_int_eq, integral_finsetSum Finset.univ (fun β _ =>
        (integrable_massShellWeight_mul_kernel hm hC (β ∘ Fin.rev) hz_rev).const_mul _)]
      refine Finset.sum_congr rfl (fun β _ => ?_)
      rw [integral_const_mul, massShellTwoPointH_two]

theorem massShellTwoPointOSHermiticity {R : HolomorphicLorentzRep ι}
    (S : StarStructure R) {m : ℝ} (hm : 0 < m)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q) :
    OSHermiticity S (massShellTwoPointS m hm C hC) :=
  schwingerFromTube_os_hermiticity S (massShellTwoPointTubeExtension m hm C hC)
    (massShellTwoPointTubeWickHermiticity S hm hC hC_herm)

theorem massShellTwoPointTubePCT (R : HolomorphicLorentzRep ι) {η : ℂ}
    {m : ℝ} (hm : 0 < m) {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (hC : MassShellCoeffData m C)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q) :
    TubePCT η R (massShellTwoPointTubeExtension m hm C hC) := by
  intro n α z hz
  match n with
  | 0 =>
      have hα : α = Fin.elim0 := Subsingleton.elim _ _
      subst hα
      simp [massShellTwoPointTubeExtension_H]
  | 1 =>
      simp [massShellTwoPointTubeExtension_H]
  | _ + 3 =>
      simp [massShellTwoPointTubeExtension_H]
  | 2 =>
      rw [two_mul_two_sub_one_div_two, pow_one]
      change massShellTwoPointH m C 2 α (-(z ∘ Fin.rev)) =
        η * ∑ β : Fin 2 → ι,
          (∏ i : Fin 2, R.σ (-1, 1) (α i) (β i)) *
            massShellTwoPointH m C 2 (β ∘ Fin.rev) z
      rw [massShellTwoPointH_two]
      have h_int_eq :
          (∫ p : Fin 3 → ℝ, massShellWeight m C α p *
            vladimirov_kernel 2 (-(z ∘ Fin.rev)) (twoPointMomentum (massShellVec m p))) =
          ∫ p : Fin 3 → ℝ, ∑ β : Fin 2 → ι,
            (η * ∏ i : Fin 2, R.σ (-1, 1) (α i) (β i)) *
              (massShellWeight m C (β ∘ Fin.rev) p *
                vladimirov_kernel 2 z (twoPointMomentum (massShellVec m p))) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        dsimp only [massShellWeight]
        rw [vladimirov_kernel_neg_rev_twoPointMomentum,
            hC_pct (massShellVec m p) α, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun β _ => by ring)
      rw [h_int_eq, integral_finsetSum Finset.univ (fun β _ =>
        (integrable_massShellWeight_mul_kernel hm hC (β ∘ Fin.rev) hz).const_mul _),
        Finset.mul_sum]
      refine Finset.sum_congr rfl (fun β _ => ?_)
      rw [integral_const_mul, massShellTwoPointH_two, mul_assoc]

theorem massShellTwoPointWightmanPCT (R : HolomorphicLorentzRep ι) {η : ℂ}
    {m : ℝ} (hm : 0 < m) {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (hC : MassShellCoeffData m C)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q) :
    WightmanPCT η R (massShellTwoPointW m C hC) :=
  wightman_pct_of_tubePCT_general R (massShellTwoPointW m C hC)
    (massShellTwoPointTubeExtension m hm C hC)
    (massShellTwoPointTubePCT R hm hC hC_pct)
    (massShellTwoPointTubeTranslationInvariant hm hC)

theorem massShellTwoPointWeakLocality (R : HolomorphicLorentzRep ι) {η : ℂ}
    {m : ℝ} (hm : 0 < m) {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R.rep A (α i) (β i)) * C β q)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q) :
    WeakLocality η (massShellTwoPointW m C hC) :=
  weakLocality_of_tubePCT R (massShellTwoPointW m C hC)
    (massShellTwoPointTubeExtension m hm C hC)
    (massShellTwoPointTubeCovariant R hm hC hC_cov)
    (massShellTwoPointTubePCT R hm hC hC_pct)

def OneParticlePositivity {R : HolomorphicLorentzRep ι}
    (S : StarStructure R) (W : WightmanFamily ι) : Prop :=
  ∀ (N : ℕ), N ≤ 1 →
    ∀ (F : ∀ j : ℕ, (Fin j → ι) → SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
      (G : ∀ j k : ℕ, (Fin j → ι) → (Fin k → ι) →
        SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ),
      (∀ j k α α' (x : Fin (j + k) → Fin 4 → ℝ),
        G j k α α' x =
          (starRingEnd ℂ) (F j α (fun i => x (Fin.castAdd k (Fin.rev i)))) *
            F k α' (fun i => x (Fin.natAdd j i))) →
      0 ≤ ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
        ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
          (∏ i, S.C (α i) (β i)) * W (j + k) (Fin.append (β ∘ Fin.rev) α') (G j k α α')

theorem oneParticlePositivity_of_positivity {R : HolomorphicLorentzRep ι}
    {S : StarStructure R} {W : WightmanFamily ι} (hpos : Positivity S W) :
    OneParticlePositivity S W :=
  fun N _hN F G hG => hpos N F G hG

lemma minkowskiFourier_split_one_one_twoPointMomentum (q : Fin 4 → ℝ)
    (f₁ f₂ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (g : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ)
    (hg : ∀ x : Fin 2 → Fin 4 → ℝ,
      g x = (starRingEnd ℂ) (f₁ (fun i => x (Fin.castAdd 1 (Fin.rev i)))) *
        f₂ (fun i => x (Fin.natAdd 1 i))) :
    minkowskiFourier g (twoPointMomentum q) =
      (starRingEnd ℂ) (minkowskiFourier f₁ (fun _ => -q)) *
        minkowskiFourier f₂ (fun _ => -q) := by
  have h := minkowskiFourier_split_rev_mul 1 1 f₁ f₂ g hg (twoPointMomentum q)
  have hL : (fun i : Fin 1 => -twoPointMomentum q (Fin.castAdd 1 (Fin.rev i))) =
      fun _ => -q := by
    ext i μ
    fin_cases i
    rfl
  have hR : (fun i : Fin 1 => twoPointMomentum q (Fin.natAdd 1 i)) =
      fun _ => -q := by
    ext i μ
    fin_cases i
    simp [twoPointMomentum]
  rw [h, hL, hR]

theorem massShellTwoPoint_nondeg_and_not_zeroMomentum {κ : Type*} {m : ℝ} (hm : 0 < m)
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (α : Fin 2 → κ) {r : (Fin 3 → ℝ) → ℝ}
    (hr_cont : Continuous r) (hr_pos : ∀ p : Fin 3 → ℝ, 0 < r p)
    (hr_eq : ∀ p : Fin 3 → ℝ, C α (massShellVec m p) = (r p : ℂ)) :
    massShellTwoPointW m C hC 2 α ≠ 0 ∧
      ¬ ZeroMomentumSpectrumCondition (massShellTwoPointW m C hC) := by
  let R : ℝ := m + 1
  have hR : 0 < R := by linarith
  let z₁ : Fin 2 → Fin 4 → ℂ :=
    fun i μ => if i = 0 ∧ μ = 0 then -Complex.I else 0
  let f₀ : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ :=
    invMinkowskiFourierCLM 2 (vladimirov_psi_schwartz 2 R hR 0)
  let f₁ : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ :=
    invMinkowskiFourierCLM 2 (vladimirov_psi_schwartz 2 R hR z₁)
  let f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ := f₀ - f₁
  have hf_zero : minkowskiFourier f 0 = 0 := by
    dsimp [f, f₀, f₁]
    rw [minkowskiFourier_sub, minkowskiFourier_invMinkowskiFourierCLM_all,
        minkowskiFourier_invMinkowskiFourierCLM_all]
    change vladimirov_psi 2 R hR 0 0 - vladimirov_psi 2 R hR z₁ 0 = 0
    simp [vladimirov_psi, vladimirov_kernel, minkowskiInnerC]
  let s : (Fin 3 → ℝ) → (Fin 2 → Fin 4 → ℝ) :=
    fun p => twoPointMomentum (massShellVec m p)
  have hs_cont : Continuous s :=
    continuous_pi (fun i => by
      fin_cases i
      · exact continuous_massShellVec m
      · exact (continuous_massShellVec m).neg)
  let F_real : (Fin 3 → ℝ) → ℝ := fun p =>
    (2 * massShellEnergy m p)⁻¹ * r p *
      (vladimirovCutoffBump 2 R hR (s p) : ℝ) * (1 - Real.exp (-(massShellEnergy m p)))
  have h_integrand_eq : ∀ p : Fin 3 → ℝ,
      massShellWeight m C α p * minkowskiFourier f (twoPointMomentum (massShellVec m p)) =
        ((F_real p : ℝ) : ℂ) := by
    intro p
    dsimp [f, f₀, f₁]
    rw [minkowskiFourier_sub, minkowskiFourier_invMinkowskiFourierCLM_all,
        minkowskiFourier_invMinkowskiFourierCLM_all]
    change massShellWeight m C α p *
      (vladimirov_psi 2 R hR 0 (s p) - vladimirov_psi 2 R hR z₁ (s p)) = _
    have h_ker0 : vladimirov_kernel 2 0 (s p) = 1 := by
      simp [vladimirov_kernel, minkowskiInnerC]
    have h_ker1 : vladimirov_kernel 2 z₁ (s p) =
        ((Real.exp (-(massShellEnergy m p)) : ℝ) : ℂ) := by
      unfold vladimirov_kernel
      rw [Complex.ofReal_exp]
      congr 1
      rw [Fin.sum_univ_two]
      simp only [Fin.isValue, z₁, true_and, false_and, ↓reduceIte,
        Fin.reduceEq, minkowskiInnerC, mul_zero, sub_zero, add_zero, s,
        twoPointMomentum_zero, massShellVec, Matrix.cons_val_zero]
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    dsimp [vladimirov_psi, massShellWeight, F_real]
    rw [hr_eq p, h_ker0, h_ker1]
    push_cast
    ring
  have hF_cont : Continuous F_real := by
    dsimp [F_real]
    have h_inv_cont : Continuous (fun p : Fin 3 → ℝ => (2 * massShellEnergy m p)⁻¹) :=
      (continuous_const.mul (continuous_massShellEnergy m)).inv₀
        (fun p => (mul_pos zero_lt_two (massShellEnergy_pos hm p)).ne')
    exact ((h_inv_cont.mul hr_cont).mul
      ((vladimirovCutoffBump 2 R hR).continuous.comp hs_cont)).mul
      (continuous_const.sub (Real.continuous_exp.comp (continuous_massShellEnergy m).neg))
  have hF_int : Integrable F_real volume := by
    have h_re_int := Complex.reCLM.integrable_comp
      (integrable_massShellWeight_mul_minkowskiFourier hC α f)
    refine h_re_int.congr (Filter.Eventually.of_forall (fun p => ?_))
    change (massShellWeight m C α p *
      minkowskiFourier f (twoPointMomentum (massShellVec m p))).re = F_real p
    rw [h_integrand_eq p, Complex.ofReal_re]
  have hF_nn : 0 ≤ F_real := by
    intro p
    dsimp [F_real]
    have h1 : 0 ≤ (2 * massShellEnergy m p)⁻¹ :=
      inv_nonneg.mpr (mul_pos zero_lt_two (massShellEnergy_pos hm p)).le
    have h2 : 0 ≤ r p := (hr_pos p).le
    have h3 : 0 ≤ (vladimirovCutoffBump 2 R hR (s p) : ℝ) :=
      (vladimirovCutoffBump 2 R hR).nonneg' (s p)
    have h4 : 0 ≤ 1 - Real.exp (-(massShellEnergy m p)) := by
      have hexp : Real.exp (-(massShellEnergy m p)) < 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.mpr (neg_lt_zero.mpr (massShellEnergy_pos hm p))
      linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4
  have hF_0_ne : F_real 0 ≠ 0 := by
    have hs0_le : ‖s 0‖ ≤ R := by
      have hp0_norm : ‖twoPointMomentum (massShellVec m 0)‖ ≤ m := by
        refine (pi_norm_le_iff_of_nonneg hm.le).mpr (fun i => ?_)
        refine (pi_norm_le_iff_of_nonneg hm.le).mpr (fun μ => ?_)
        have hω0 : massShellEnergy m 0 = m := by
          unfold massShellEnergy massShellSpatialSq
          simp [Real.sqrt_sq hm.le]
        fin_cases i <;> fin_cases μ <;>
          simp [twoPointMomentum, massShellVec, hω0, Real.norm_eq_abs, abs_of_pos hm, hm.le]
      dsimp [s, R]
      linarith
    have h_bump0 : (vladimirovCutoffBump 2 R hR (s 0) : ℝ) = 1 := by
      apply (vladimirovCutoffBump 2 R hR).one_of_mem_closedBall
      rw [Metric.mem_closedBall, dist_zero_right]
      dsimp [vladimirovCutoffBump]
      exact hs0_le
    dsimp [F_real]
    rw [h_bump0, mul_one]
    have hexp : Real.exp (-(massShellEnergy m 0)) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (neg_lt_zero.mpr (massShellEnergy_pos hm 0))
    have h_pos : 0 < (2 * massShellEnergy m 0)⁻¹ * r 0 *
        (1 - Real.exp (-(massShellEnergy m 0))) :=
      mul_pos
        (mul_pos (inv_pos.mpr (mul_pos zero_lt_two (massShellEnergy_pos hm 0))) (hr_pos 0))
        (by linarith)
    exact h_pos.ne'
  have h_int_pos : 0 < ∫ p : Fin 3 → ℝ, F_real p :=
    MeasureTheory.integral_pos_of_integrable_nonneg_nonzero hF_cont hF_int hF_nn hF_0_ne
  have hWf_eq : massShellTwoPointW m C hC 2 α f = ((∫ p : Fin 3 → ℝ, F_real p : ℝ) : ℂ) := by
    rw [massShellTwoPointW_two_apply]
    have h_fn :
        (fun p : Fin 3 → ℝ =>
          massShellWeight m C α p *
            minkowskiFourier f (twoPointMomentum (massShellVec m p))) =
        fun p : Fin 3 → ℝ => ((F_real p : ℝ) : ℂ) :=
      funext h_integrand_eq
    rw [h_fn, integral_complex_ofReal]
  have hWf_ne : massShellTwoPointW m C hC 2 α f ≠ 0 := by
    rw [hWf_eq]
    exact Complex.ofReal_ne_zero.mpr h_int_pos.ne'
  refine ⟨fun hW0 => hWf_ne (by rw [hW0]; rfl), fun hspec => ?_⟩
  exact hWf_ne (hspec 2 α f hf_zero)

def massiveKGCoeff : (Fin 2 → Unit) → (Fin 4 → ℝ) → ℂ :=
  fun _ _ => 1

lemma massiveKGCoeff_data {m : ℝ} (hm : 0 < m) :
    MassShellCoeffData m massiveKGCoeff := by
  refine ⟨fun _ => measurable_const, fun _ => ⟨(2 * m)⁻¹, by positivity, fun p => ?_⟩⟩
  dsimp [massShellWeight, massiveKGCoeff]
  have h_cast : (2 : ℂ) * (massShellEnergy m p : ℂ) = ((2 * massShellEnergy m p : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [mul_one, h_cast, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (mul_pos zero_lt_two (massShellEnergy_pos hm p)).le]
  exact inv_anti₀ (mul_pos zero_lt_two hm)
    (mul_le_mul_of_nonneg_left (massShellEnergy_ge_mass hm p) zero_le_two)

noncomputable def massiveKGW (m : ℝ) (hm : 0 < m) : WightmanFamily Unit :=
  massShellTwoPointW m massiveKGCoeff (massiveKGCoeff_data hm)

noncomputable def massiveKGTubeExtension (m : ℝ) (hm : 0 < m) :
    TubeExtension (massiveKGW m hm) :=
  massShellTwoPointTubeExtension m hm massiveKGCoeff (massiveKGCoeff_data hm)

noncomputable def massiveKGS (m : ℝ) (hm : 0 < m) : SchwingerFamily Unit :=
  massShellTwoPointS m hm massiveKGCoeff (massiveKGCoeff_data hm)

theorem massiveKG_forwardConeSpectrumCondition {m : ℝ} (hm : 0 < m) :
    ForwardConeSpectrumCondition (massiveKGW m hm) :=
  massShellTwoPoint_forwardConeSpectrumCondition hm (massiveKGCoeff_data hm)

theorem massiveKGS_vacuumNormalized {m : ℝ} (hm : 0 < m) :
    OSVacuumNormalized (massiveKGS m hm) :=
  massShellTwoPointS_vacuumNormalized m hm massiveKGCoeff (massiveKGCoeff_data hm)

theorem massiveKGTubeTranslationInvariant {m : ℝ} (hm : 0 < m) :
    TubeTranslationInvariant (massiveKGTubeExtension m hm) :=
  massShellTwoPointTubeTranslationInvariant hm (massiveKGCoeff_data hm)

theorem massiveKGOSTranslationInvariant {m : ℝ} (hm : 0 < m) :
    OSTranslationInvariant (massiveKGS m hm) :=
  massShellTwoPointOSTranslationInvariant hm (massiveKGCoeff_data hm)

theorem massiveKGTubeCovariant {m : ℝ} (hm : 0 < m) :
    TubeCovariant trivialRep (massiveKGTubeExtension m hm) :=
  massShellTwoPointTubeCovariant trivialRep hm (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])

theorem massiveKGPoincareCovariant {m : ℝ} (hm : 0 < m) :
    PoincareCovariant trivialRep (massiveKGW m hm) :=
  massShellTwoPointPoincareCovariant trivialRep hm (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])

theorem massiveKGTubeWickHermiticity {m : ℝ} (hm : 0 < m) :
    TubeWickHermiticity trivialStarStructure (massiveKGTubeExtension m hm) :=
  massShellTwoPointTubeWickHermiticity trivialStarStructure hm (massiveKGCoeff_data hm)
    (fun _ _ => by simp [massiveKGCoeff, trivialStarStructure])

theorem massiveKGOSHermiticity {m : ℝ} (hm : 0 < m) :
    OSHermiticity trivialStarStructure (massiveKGS m hm) :=
  massShellTwoPointOSHermiticity trivialStarStructure hm (massiveKGCoeff_data hm)
    (fun _ _ => by simp [massiveKGCoeff, trivialStarStructure])

theorem massiveKGTubePCT {m : ℝ} (hm : 0 < m) :
    TubePCT 1 trivialRep (massiveKGTubeExtension m hm) :=
  massShellTwoPointTubePCT trivialRep hm (massiveKGCoeff_data hm)
    (fun _ _ => by simp [massiveKGCoeff, trivialRep])

theorem massiveKGTubeWeakLocality {m : ℝ} (hm : 0 < m) :
    TubeWeakLocality 1 (massiveKGTubeExtension m hm) := by
  intro n α z hz
  have hpct := massiveKGTubePCT hm n α z hz
  simpa [trivialRep] using hpct

theorem massiveKGWightmanPCT {m : ℝ} (hm : 0 < m) :
    WightmanPCT 1 trivialRep (massiveKGW m hm) :=
  massShellTwoPointWightmanPCT trivialRep hm (massiveKGCoeff_data hm)
    (fun _ _ => by simp [massiveKGCoeff, trivialRep])

theorem massiveKGWeakLocality {m : ℝ} (hm : 0 < m) :
    WeakLocality 1 (massiveKGW m hm) :=
  massShellTwoPointWeakLocality trivialRep hm (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])
    (fun _ _ => by simp [massiveKGCoeff, trivialRep])

theorem massiveKGOneParticlePositivity {m : ℝ} (hm : 0 < m) :
    OneParticlePositivity trivialStarStructure (massiveKGW m hm) := by
  intro N hN F G hG
  have h_zero_term :
      0 ≤ ∑ α : Fin 0 → Unit, ∑ α' : Fin 0 → Unit, ∑ β : Fin 0 → Unit,
        (∏ i, trivialStarStructure.C (α i) (β i)) *
          massiveKGW m hm 0 (Fin.append (β ∘ Fin.rev) α') (G 0 0 α α') := by
    simp only [Fintype.sum_unique, trivialStarStructure, Matrix.one_apply_eq,
      Finset.prod_const_one, one_mul, massiveKGW, massShellTwoPointW_zero_apply]
    have hg0 := hG 0 0 default default 0
    have hL0 : (fun i : Fin 0 => (0 : Fin 0 → Fin 4 → ℝ) (Fin.castAdd 0 (Fin.rev i))) = 0 :=
      Subsingleton.elim _ _
    have hR0 : (fun i : Fin 0 => (0 : Fin 0 → Fin 4 → ℝ) (Fin.natAdd 0 i)) = 0 :=
      Subsingleton.elim _ _
    rw [hg0, hL0, hR0, mul_comm, Complex.mul_conj]
    exact_mod_cast Complex.normSq_nonneg (F 0 default 0)
  interval_cases N
  · simpa [Finset.range_one] using h_zero_term
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have h01 :
        (∑ α : Fin 0 → Unit, ∑ α' : Fin 1 → Unit, ∑ β : Fin 0 → Unit,
          (∏ i, trivialStarStructure.C (α i) (β i)) *
            massiveKGW m hm 1 (Fin.append (β ∘ Fin.rev) α') (G 0 1 α α')) = 0 := by
      simp [massiveKGW]
    have h10 :
        (∑ α : Fin 1 → Unit, ∑ α' : Fin 0 → Unit, ∑ β : Fin 1 → Unit,
          (∏ i, trivialStarStructure.C (α i) (β i)) *
            massiveKGW m hm 1 (Fin.append (β ∘ Fin.rev) α') (G 1 0 α α')) = 0 := by
      simp [massiveKGW]
    have h11 :
        0 ≤ ∑ α : Fin 1 → Unit, ∑ α' : Fin 1 → Unit, ∑ β : Fin 1 → Unit,
          (∏ i, trivialStarStructure.C (α i) (β i)) *
            massiveKGW m hm 2 (Fin.append (β ∘ Fin.rev) α') (G 1 1 α α') := by
      simp only [Fintype.sum_unique, trivialStarStructure, Matrix.one_apply_eq,
        Finset.prod_const_one, one_mul, massiveKGW, massShellTwoPointW_two_apply]
      refine complex_integral_nonneg
        (integrable_massShellWeight_mul_minkowskiFourier
          (massiveKGCoeff_data hm) _ (G 1 1 default default))
        (fun p => ?_)
      dsimp only [massShellWeight, massiveKGCoeff]
      rw [mul_one,
          minkowskiFourier_split_one_one_twoPointMomentum (massShellVec m p)
            (F 1 default) (F 1 default) (G 1 1 default default)
            (hG 1 1 default default),
          mul_comm ((starRingEnd ℂ) _), Complex.mul_conj]
      have h_pos : 0 ≤ (2 * massShellEnergy m p)⁻¹ *
          Complex.normSq (minkowskiFourier (F 1 default) (fun _ => -massShellVec m p)) :=
        mul_nonneg
          (inv_nonneg.mpr (mul_pos zero_lt_two (massShellEnergy_pos hm p)).le)
          (Complex.normSq_nonneg _)
      exact_mod_cast h_pos
    rw [h01, h10, add_zero]
    exact add_nonneg h_zero_term (add_nonneg le_rfl h11)

theorem massiveKGW_twoPoint_ne_zero {m : ℝ} (hm : 0 < m) :
    massiveKGW m hm 2 default ≠ 0 :=
  (massShellTwoPoint_nondeg_and_not_zeroMomentum hm (massiveKGCoeff_data hm) default
    continuous_const (fun _ => zero_lt_one) (fun _ => Complex.ofReal_one.symm)).1

theorem not_zeroMomentumSpectrumCondition_massiveKGW {m : ℝ} (hm : 0 < m) :
    ¬ ZeroMomentumSpectrumCondition (massiveKGW m hm) :=
  (massShellTwoPoint_nondeg_and_not_zeroMomentum hm (massiveKGCoeff_data hm) default
    continuous_const (fun _ => zero_lt_one) (fun _ => Complex.ofReal_one.symm)).2

theorem massiveKG_spin_statistics {m : ℝ} (hm : 0 < m) {η : ℂ}
    (hloc : WeakLocality η (massiveKGW m hm)) :
    η = 1 :=
  spin_statistics_of_tubePCT_and_weakLocality trivialRep (massiveKGW m hm)
    (massiveKGTubeExtension m hm) (massiveKGTubeCovariant hm) (massiveKGTubePCT hm)
    hloc ⟨default, massiveKGW_twoPoint_ne_zero hm⟩

theorem not_fermionic_weakLocality_massiveKGW {m : ℝ} (hm : 0 < m) :
    ¬ WeakLocality (-1) (massiveKGW m hm) := by
  intro hferm
  have h := massiveKG_spin_statistics hm hferm
  norm_num at h

theorem massiveKG_master {m : ℝ} (hm : 0 < m) :
    ForwardConeSpectrumCondition (massiveKGW m hm) ∧
    ¬ ZeroMomentumSpectrumCondition (massiveKGW m hm) ∧
    massiveKGW m hm 2 default ≠ 0 ∧
    PoincareCovariant trivialRep (massiveKGW m hm) ∧
    TubeCovariant trivialRep (massiveKGTubeExtension m hm) ∧
    TubeTranslationInvariant (massiveKGTubeExtension m hm) ∧
    TubeWickHermiticity trivialStarStructure (massiveKGTubeExtension m hm) ∧
    TubePCT 1 trivialRep (massiveKGTubeExtension m hm) ∧
    WightmanPCT 1 trivialRep (massiveKGW m hm) ∧
    WeakLocality 1 (massiveKGW m hm) ∧
    OneParticlePositivity trivialStarStructure (massiveKGW m hm) ∧
    (∀ η : ℂ, WeakLocality η (massiveKGW m hm) → η = 1) :=
  ⟨massiveKG_forwardConeSpectrumCondition hm,
   not_zeroMomentumSpectrumCondition_massiveKGW hm,
   massiveKGW_twoPoint_ne_zero hm,
   massiveKGPoincareCovariant hm,
   massiveKGTubeCovariant hm,
   massiveKGTubeTranslationInvariant hm,
   massiveKGTubeWickHermiticity hm,
   massiveKGTubePCT hm,
   massiveKGWightmanPCT hm,
   massiveKGWeakLocality hm,
   massiveKGOneParticlePositivity hm,
   fun _ hloc => massiveKG_spin_statistics hm hloc⟩

noncomputable def diracSlashCoeff (q : Fin 4 → ℝ) (α : Fin 2 → Fin 2 ⊕ Fin 2) : ℂ :=
  match α 0, α 1 with
  | Sum.inl a, Sum.inr b => vec_to_spinor (fun μ => (q μ : ℂ)) a b
  | Sum.inr a, Sum.inl b => vec_to_spinor (fun μ => (q μ : ℂ)) b a
  | _, _ => 0

@[simp]
lemma diracSlashCoeff_inl_inl (q : Fin 4 → ℝ) (a b : Fin 2) :
    diracSlashCoeff q ![Sum.inl a, Sum.inl b] = 0 := rfl

@[simp]
lemma diracSlashCoeff_inr_inr (q : Fin 4 → ℝ) (a b : Fin 2) :
    diracSlashCoeff q ![Sum.inr a, Sum.inr b] = 0 := rfl

@[simp]
lemma diracSlashCoeff_inl_inr (q : Fin 4 → ℝ) (a b : Fin 2) :
    diracSlashCoeff q ![Sum.inl a, Sum.inr b] =
      vec_to_spinor (fun μ => (q μ : ℂ)) a b := rfl

@[simp]
lemma diracSlashCoeff_inr_inl (q : Fin 4 → ℝ) (a b : Fin 2) :
    diracSlashCoeff q ![Sum.inr a, Sum.inl b] =
      vec_to_spinor (fun μ => (q μ : ℂ)) b a := rfl

noncomputable def diracMassShellCoeff (m : ℝ)
    (α : Fin 2 → Fin 2 ⊕ Fin 2) (q : Fin 4 → ℝ) : ℂ :=
  (m : ℂ) * diracEpsilon α + diracSlashCoeff q α

lemma norm_vec_to_spinor_massShellVec_le {m : ℝ} (hm : 0 < m)
    (p : Fin 3 → ℝ) (a b : Fin 2) :
    ‖vec_to_spinor (fun μ => (massShellVec m p μ : ℂ)) a b‖ ≤
      2 * massShellEnergy m p := by
  have hω : 0 ≤ massShellEnergy m p := (massShellEnergy_pos hm p).le
  have hp0 : |p 0| ≤ massShellEnergy m p := abs_coord_le_massShellEnergy hm p 0
  have hp1 : |p 1| ≤ massShellEnergy m p := abs_coord_le_massShellEnergy hm p 1
  have hp2 : |p 2| ≤ massShellEnergy m p := abs_coord_le_massShellEnergy hm p 2
  revert a b
  refine Fin.forall_fin_two.mpr
    ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
  · rw [vec_to_spinor_apply_00]
    dsimp [massShellVec]
    calc ‖(massShellEnergy m p : ℂ) + (p 2 : ℂ)‖
        ≤ ‖(massShellEnergy m p : ℂ)‖ + ‖(p 2 : ℂ)‖ := norm_add_le _ _
      _ = |massShellEnergy m p| + |p 2| := by
          simp [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 2 * massShellEnergy m p := by rw [abs_of_nonneg hω]; linarith
  · rw [vec_to_spinor_apply_01]
    dsimp [massShellVec]
    calc ‖(p 0 : ℂ) - (p 1 : ℂ) * Complex.I‖
        ≤ ‖(p 0 : ℂ)‖ + ‖(p 1 : ℂ) * Complex.I‖ := norm_sub_le _ _
      _ = |p 0| + |p 1| := by
          simp [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 2 * massShellEnergy m p := by linarith
  · rw [vec_to_spinor_apply_10]
    dsimp [massShellVec]
    calc ‖(p 0 : ℂ) + (p 1 : ℂ) * Complex.I‖
        ≤ ‖(p 0 : ℂ)‖ + ‖(p 1 : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |p 0| + |p 1| := by
          simp [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 2 * massShellEnergy m p := by linarith
  · rw [vec_to_spinor_apply_11]
    dsimp [massShellVec]
    calc ‖(massShellEnergy m p : ℂ) - (p 2 : ℂ)‖
        ≤ ‖(massShellEnergy m p : ℂ)‖ + ‖(p 2 : ℂ)‖ := norm_sub_le _ _
      _ = |massShellEnergy m p| + |p 2| := by
          simp [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 2 * massShellEnergy m p := by rw [abs_of_nonneg hω]; linarith

lemma norm_diracSlashCoeff_massShellVec_le {m : ℝ} (hm : 0 < m)
    (p : Fin 3 → ℝ) (α : Fin 2 → Fin 2 ⊕ Fin 2) :
    ‖diracSlashCoeff (massShellVec m p) α‖ ≤ 2 * massShellEnergy m p := by
  have hω : 0 ≤ massShellEnergy m p := (massShellEnergy_pos hm p).le
  rw [finTwo_eq_vecCons α]
  rcases α 0 with a | a <;> rcases α 1 with b | b
  · rw [diracSlashCoeff_inl_inl, norm_zero]
    linarith
  · rw [diracSlashCoeff_inl_inr]
    exact norm_vec_to_spinor_massShellVec_le hm p a b
  · rw [diracSlashCoeff_inr_inl]
    exact norm_vec_to_spinor_massShellVec_le hm p b a
  · rw [diracSlashCoeff_inr_inr, norm_zero]
    linarith

lemma diracMassShellCoeff_data {m : ℝ} (hm : 0 < m) :
    MassShellCoeffData m (diracMassShellCoeff m) := by
  refine ⟨fun α => ?_, fun α => ⟨3 / 2, by norm_num, fun p => ?_⟩⟩
  · unfold diracMassShellCoeff
    refine measurable_const.add ?_
    have h_entry : ∀ a b : Fin 2,
        Continuous (fun p : Fin 3 → ℝ =>
          vec_to_spinor (fun μ => (massShellVec m p μ : ℂ)) a b) := by
      intro a b
      have hc : ∀ μ : Fin 4,
          Continuous (fun p : Fin 3 → ℝ => (massShellVec m p μ : ℂ)) :=
        fun μ => Complex.continuous_ofReal.comp
          ((continuous_apply μ).comp (continuous_massShellVec m))
      revert a b
      refine Fin.forall_fin_two.mpr
        ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
      · rw [show (fun p : Fin 3 → ℝ =>
            vec_to_spinor (fun μ => (massShellVec m p μ : ℂ)) 0 0) =
            fun p => (massShellVec m p 0 : ℂ) + (massShellVec m p 3 : ℂ) by
          ext p; exact vec_to_spinor_apply_00 _]
        exact (hc 0).add (hc 3)
      · rw [show (fun p : Fin 3 → ℝ =>
            vec_to_spinor (fun μ => (massShellVec m p μ : ℂ)) 0 1) =
            fun p => (massShellVec m p 1 : ℂ) - (massShellVec m p 2 : ℂ) * Complex.I by
          ext p; exact vec_to_spinor_apply_01 _]
        exact (hc 1).sub ((hc 2).mul continuous_const)
      · rw [show (fun p : Fin 3 → ℝ =>
            vec_to_spinor (fun μ => (massShellVec m p μ : ℂ)) 1 0) =
            fun p => (massShellVec m p 1 : ℂ) + (massShellVec m p 2 : ℂ) * Complex.I by
          ext p; exact vec_to_spinor_apply_10 _]
        exact (hc 1).add ((hc 2).mul continuous_const)
      · rw [show (fun p : Fin 3 → ℝ =>
            vec_to_spinor (fun μ => (massShellVec m p μ : ℂ)) 1 1) =
            fun p => (massShellVec m p 0 : ℂ) - (massShellVec m p 3 : ℂ) by
          ext p; exact vec_to_spinor_apply_11 _]
        exact (hc 0).sub (hc 3)
    rw [finTwo_eq_vecCons α]
    rcases α 0 with a | a <;> rcases α 1 with b | b
    · exact measurable_const
    · exact (h_entry a b).measurable
    · exact (h_entry b a).measurable
    · exact measurable_const
  · have hω_pos : 0 < massShellEnergy m p := massShellEnergy_pos hm p
    have hm_le : m ≤ massShellEnergy m p := massShellEnergy_ge_mass hm p
    have h_eps : ‖(m : ℂ) * diracEpsilon α‖ ≤ massShellEnergy m p := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hm.le]
      calc m * ‖diracEpsilon α‖ ≤ m * 1 :=
            mul_le_mul_of_nonneg_left (norm_diracEpsilon_le_one α) hm.le
        _ = m := mul_one m
        _ ≤ massShellEnergy m p := hm_le
    have h_coeff : ‖diracMassShellCoeff m α (massShellVec m p)‖ ≤
        3 * massShellEnergy m p := by
      unfold diracMassShellCoeff
      calc ‖(m : ℂ) * diracEpsilon α + diracSlashCoeff (massShellVec m p) α‖
          ≤ ‖(m : ℂ) * diracEpsilon α‖ + ‖diracSlashCoeff (massShellVec m p) α‖ :=
            norm_add_le _ _
        _ ≤ massShellEnergy m p + 2 * massShellEnergy m p :=
            add_le_add h_eps (norm_diracSlashCoeff_massShellVec_le hm p α)
        _ = 3 * massShellEnergy m p := by ring
    dsimp [massShellWeight]
    have h_cast : (2 : ℂ) * (massShellEnergy m p : ℂ) =
        ((2 * massShellEnergy m p : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [norm_mul, h_cast, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (mul_pos zero_lt_two hω_pos).le]
    calc (2 * massShellEnergy m p)⁻¹ * ‖diracMassShellCoeff m α (massShellVec m p)‖
        ≤ (2 * massShellEnergy m p)⁻¹ * (3 * massShellEnergy m p) :=
          mul_le_mul_of_nonneg_left h_coeff
            (inv_nonneg.mpr (mul_pos zero_lt_two hω_pos).le)
      _ = 3 / 2 := by field_simp [hω_pos.ne']

theorem sum_diracRep_mul_diracSlashCoeff (A : SL2C) (q : Fin 4 → ℝ)
    (α : Fin 2 → Fin 2 ⊕ Fin 2) :
    (∑ β : Fin 2 → Fin 2 ⊕ Fin 2,
      (∏ i : Fin 2, diracRep.rep A (α i) (β i)) * diracSlashCoeff q β) =
      diracSlashCoeff ((lorentzOfSL2C A).mulVec q) α := by
  rw [sum_fin_two_fun (ι := Fin 2 ⊕ Fin 2)]
  simp only [Fintype.sum_sum_type, Fin.prod_univ_two, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, diracSlashCoeff_inl_inl,
    diracSlashCoeff_inr_inr, mul_zero, zero_add, add_zero,
    Finset.sum_const_zero]
  rw [finTwo_eq_vecCons α]
  rcases α 0 with a | a <;> rcases α 1 with b | b
  · have h_ir : ∀ y : Fin 2,
        diracRep.rep A (Sum.inl b) (Sum.inr y) = 0 := fun _ => rfl
    have h_ri : ∀ x : Fin 2,
        diracRep.rep A (Sum.inl a) (Sum.inr x) = 0 := fun _ => rfl
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, h_ir, h_ri]
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have h_ri : ∀ x : Fin 2,
        diracRep.rep A (Sum.inl a) (Sum.inr x) = 0 := fun _ => rfl
    have h_ll : ∀ x : Fin 2,
        diracRep.rep A (Sum.inl a) (Sum.inl x) = A.1 a x := fun _ => rfl
    have h_rr : ∀ y : Fin 2,
        diracRep.rep A (Sum.inr b) (Sum.inr y) = star (A.1 b y) := fun _ => rfl
    simp only [h_ri, zero_mul, Finset.sum_const_zero, add_zero,
      h_ll, h_rr, diracSlashCoeff_inl_inr]
    rw [vec_to_spinor_lorentzOfSL2C_coe A q, Matrix.mul_apply]
    simp_rw [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    have h_star : (star A.1) x b = star (A.1 b x) := rfl
    rw [h_star]
    ring
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have h_ir : ∀ x : Fin 2,
        diracRep.rep A (Sum.inr a) (Sum.inl x) = 0 := fun _ => rfl
    have h_rr : ∀ x : Fin 2,
        diracRep.rep A (Sum.inr a) (Sum.inr x) = star (A.1 a x) := fun _ => rfl
    have h_ll : ∀ y : Fin 2,
        diracRep.rep A (Sum.inl b) (Sum.inl y) = A.1 b y := fun _ => rfl
    simp only [h_ir, zero_mul, Finset.sum_const_zero, zero_add,
      h_rr, h_ll, diracSlashCoeff_inr_inl]
    rw [vec_to_spinor_lorentzOfSL2C_coe A q, Matrix.mul_apply]
    simp_rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    have h_star : (star A.1) x a = star (A.1 a x) := rfl
    rw [h_star]
    ring
  · have h_ir : ∀ x : Fin 2,
        diracRep.rep A (Sum.inr a) (Sum.inl x) = 0 := fun _ => rfl
    have h_ri : ∀ y : Fin 2,
        diracRep.rep A (Sum.inr b) (Sum.inl y) = 0 := fun _ => rfl
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, h_ir, h_ri]

theorem diracMassShellCoeff_lorentz (m : ℝ) (A : SL2C) (q : Fin 4 → ℝ)
    (α : Fin 2 → Fin 2 ⊕ Fin 2) :
    diracMassShellCoeff m α ((lorentzOfSL2C A).mulVec q) =
      ∑ β : Fin 2 → Fin 2 ⊕ Fin 2,
        (∏ i : Fin 2, diracRep.rep A (α i) (β i)) * diracMassShellCoeff m β q := by
  unfold diracMassShellCoeff
  simp_rw [mul_add, Finset.sum_add_distrib, ← mul_assoc, mul_comm _ (m : ℂ), mul_assoc,
    ← Finset.mul_sum]
  have h_eps :
      (∑ β : Fin 2 → Fin 2 ⊕ Fin 2,
        (∏ i : Fin 2, diracRep.rep A (α i) (β i)) * diracEpsilon β) =
        diracEpsilon α := by
    simpa [HolomorphicLorentzRep.rep_apply] using
      sum_diracRep_mul_diracEpsilon (A, sl2c_conj A) α
  rw [h_eps, sum_diracRep_mul_diracSlashCoeff A q α]

lemma star_vec_to_spinor_real (q : Fin 4 → ℝ) (a b : Fin 2) :
    star (vec_to_spinor (fun μ => (q μ : ℂ)) a b) =
      vec_to_spinor (fun μ => (q μ : ℂ)) b a := by
  revert a b
  refine Fin.forall_fin_two.mpr
    ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
  · rw [vec_to_spinor_apply_00, Complex.star_def, map_add,
        Complex.conj_ofReal, Complex.conj_ofReal]
  · rw [vec_to_spinor_apply_01, vec_to_spinor_apply_10, Complex.star_def,
        map_sub, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    ring
  · rw [vec_to_spinor_apply_10, vec_to_spinor_apply_01, Complex.star_def,
        map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    ring
  · rw [vec_to_spinor_apply_11, Complex.star_def, map_sub,
        Complex.conj_ofReal, Complex.conj_ofReal]

theorem star_diracSlashCoeff (q : Fin 4 → ℝ) (α : Fin 2 → Fin 2 ⊕ Fin 2) :
    star (diracSlashCoeff q α) =
      diracSlashCoeff q ((Sum.swap ∘ α) ∘ Fin.rev) := by
  rw [finTwo_eq_vecCons α]
  rcases α 0 with a | a <;> rcases α 1 with b | b
  · simp [diracSlashCoeff]
  · change star (vec_to_spinor (fun μ => (q μ : ℂ)) a b) =
      vec_to_spinor (fun μ => (q μ : ℂ)) b a
    exact star_vec_to_spinor_real q a b
  · change star (vec_to_spinor (fun μ => (q μ : ℂ)) b a) =
      vec_to_spinor (fun μ => (q μ : ℂ)) a b
    exact star_vec_to_spinor_real q b a
  · simp [diracSlashCoeff]

theorem diracMassShellCoeff_herm (m : ℝ) (q : Fin 4 → ℝ)
    (α : Fin 2 → Fin 2 ⊕ Fin 2) :
    star (diracMassShellCoeff m α q) =
      ∑ β : Fin 2 → Fin 2 ⊕ Fin 2,
        (∏ i : Fin 2, diracStarStructure.C (α i) (β i)) *
          diracMassShellCoeff m (β ∘ Fin.rev) q := by
  dsimp [diracStarStructure]
  rw [sum_prod_chiralDoubleStarStructure_C_mul leftWeylRep leftWeylRep_hasRealConj
    2 α (fun β => diracMassShellCoeff m (β ∘ Fin.rev) q)]
  unfold diracMassShellCoeff
  rw [map_add, map_mul, Complex.conj_ofReal, ← Complex.star_def,
      star_diracEpsilon, star_diracSlashCoeff]
  rfl

lemma diracRep_neg_one_one_apply (x y : Fin 2 ⊕ Fin 2) :
    diracRep.σ (-1, 1) x y =
      match x, y with
      | Sum.inl a, Sum.inl b => if a = b then -1 else 0
      | Sum.inr a, Sum.inr b => if a = b then 1 else 0
      | _, _ => 0 := by
  rcases x with a | a <;> rcases y with b | b
  · change ((-1 : SL2C).1 : Matrix (Fin 2) (Fin 2) ℂ) a b = if a = b then -1 else 0
    by_cases hab : a = b <;> simp [hab, Matrix.SpecialLinearGroup.coe_neg]
  · rfl
  · rfl
  · change ((1 : SL2C).1 : Matrix (Fin 2) (Fin 2) ℂ) a b = if a = b then 1 else 0
    by_cases hab : a = b <;> simp [hab]

theorem diracMassShellCoeff_pct (m : ℝ) (q : Fin 4 → ℝ)
    (α : Fin 2 → Fin 2 ⊕ Fin 2) :
    diracMassShellCoeff m α q =
      (-1 : ℂ) * ∑ β : Fin 2 → Fin 2 ⊕ Fin 2,
        (∏ i : Fin 2, diracRep.σ (-1, 1) (α i) (β i)) *
          diracMassShellCoeff m (β ∘ Fin.rev) q := by
  rw [sum_fin_two_fun (ι := Fin 2 ⊕ Fin 2)]
  simp only [Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    finTwo_comp_rev_vecCons]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [finTwo_eq_vecCons α]
  rcases α 0 with a | a <;> rcases α 1 with b | b
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fintype.sum_sum_type,
      diracRep_neg_one_one_apply, zero_mul, Finset.sum_const_zero, add_zero, ite_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      diracMassShellCoeff, diracSlashCoeff_inl_inl]
    have hrev := diracEpsilon_comp_rev ![Sum.inl a, Sum.inl b]
    rw [finTwo_comp_rev_vecCons] at hrev
    rw [hrev]
    ring
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fintype.sum_sum_type,
      diracRep_neg_one_one_apply, zero_mul, Finset.sum_const_zero, zero_add, add_zero,
      ite_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      diracMassShellCoeff, diracEpsilon_inl_inr, diracEpsilon_inr_inl,
      diracSlashCoeff_inl_inr, diracSlashCoeff_inr_inl, mul_zero]
    ring
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fintype.sum_sum_type,
      diracRep_neg_one_one_apply, zero_mul, Finset.sum_const_zero, zero_add, add_zero,
      ite_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      diracMassShellCoeff, diracEpsilon_inl_inr, diracEpsilon_inr_inl,
      diracSlashCoeff_inl_inr, diracSlashCoeff_inr_inl, mul_zero]
    ring
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fintype.sum_sum_type,
      diracRep_neg_one_one_apply, zero_mul, Finset.sum_const_zero, zero_add, ite_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      diracMassShellCoeff, diracSlashCoeff_inr_inr, add_zero]
    have hrev := diracEpsilon_comp_rev ![Sum.inr a, Sum.inr b]
    rw [finTwo_comp_rev_vecCons] at hrev
    rw [hrev]
    ring

lemma massShellEnergy_add_third_pos {m : ℝ} (hm : 0 < m) (p : Fin 3 → ℝ) :
    0 < massShellEnergy m p + p 2 := by
  have h_sq_lt : |p 2| ^ 2 < (massShellEnergy m p) ^ 2 := by
    rw [sq_abs, massShellEnergy_sq]
    unfold massShellSpatialSq
    nlinarith [sq_pos_of_pos hm, sq_nonneg (p 0), sq_nonneg (p 1)]
  have h_lt : |p 2| < massShellEnergy m p := by
    have h1 := Real.sqrt_lt_sqrt (sq_nonneg _) h_sq_lt
    rwa [Real.sqrt_sq (abs_nonneg _),
         Real.sqrt_sq (massShellEnergy_pos hm p).le] at h1
  have h_neg : -p 2 ≤ |p 2| := neg_le_abs (p 2)
  linarith

theorem diracMassShellCoeff_quad_nonneg {m : ℝ} (hm : 0 < m)
    (p : Fin 3 → ℝ) (ξ : Fin 2 ⊕ Fin 2 → ℂ) :
    0 ≤ ∑ γ : Fin 2 ⊕ Fin 2, ∑ γ' : Fin 2 ⊕ Fin 2,
      (starRingEnd ℂ) (ξ γ) *
        diracMassShellCoeff m ![Sum.swap γ, γ'] (massShellVec m p) * ξ γ' := by
  let q := massShellVec m p
  let Q : ℂ := ∑ γ : Fin 2 ⊕ Fin 2, ∑ γ' : Fin 2 ⊕ Fin 2,
    (starRingEnd ℂ) (ξ γ) * diracMassShellCoeff m ![Sum.swap γ, γ'] q * ξ γ'
  let u₀ : ℂ := ξ (Sum.inl 0)
  let u₁ : ℂ := ξ (Sum.inl 1)
  let v₀ : ℂ := ξ (Sum.inr 0)
  let v₁ : ℂ := ξ (Sum.inr 1)
  let A₀ : ℂ := ((q 0 : ℂ) + (q 3 : ℂ)) * v₀ +
    ((q 1 : ℂ) - (q 2 : ℂ) * Complex.I) * v₁ + (m : ℂ) * Complex.I * u₁
  let A₁ : ℂ := (m : ℂ) * v₁ -
    Complex.I * (((q 0 : ℂ) + (q 3 : ℂ)) * u₀ +
      ((q 1 : ℂ) + (q 2 : ℂ) * Complex.I) * u₁)
  have h_msq : (m : ℂ) ^ 2 =
      (q 0 : ℂ) ^ 2 - (q 1 : ℂ) ^ 2 - (q 2 : ℂ) ^ 2 - (q 3 : ℂ) ^ 2 := by
    have h_real : m ^ 2 = (q 0) ^ 2 - (q 1) ^ 2 - (q 2) ^ 2 - (q 3) ^ 2 := by
      dsimp [q, massShellVec]
      rw [massShellEnergy_sq]
      unfold massShellSpatialSq
      ring
    exact_mod_cast h_real
  have hQ_expand : Q =
      (starRingEnd ℂ) u₀ * (((q 0 : ℂ) + (q 3 : ℂ)) * u₀ +
        ((q 1 : ℂ) + (q 2 : ℂ) * Complex.I) * u₁) +
      (starRingEnd ℂ) u₁ * (((q 1 : ℂ) - (q 2 : ℂ) * Complex.I) * u₀ +
        ((q 0 : ℂ) - (q 3 : ℂ)) * u₁) +
      (starRingEnd ℂ) v₀ * (((q 0 : ℂ) + (q 3 : ℂ)) * v₀ +
        ((q 1 : ℂ) - (q 2 : ℂ) * Complex.I) * v₁) +
      (starRingEnd ℂ) v₁ * (((q 1 : ℂ) + (q 2 : ℂ) * Complex.I) * v₀ +
        ((q 0 : ℂ) - (q 3 : ℂ)) * v₁) +
      (m : ℂ) * Complex.I *
        ((starRingEnd ℂ) u₀ * v₁ - (starRingEnd ℂ) u₁ * v₀ +
          (starRingEnd ℂ) v₀ * u₁ - (starRingEnd ℂ) v₁ * u₀) := by
    dsimp [Q, u₀, u₁, v₀, v₁]
    simp only [Fintype.sum_sum_type, Fin.sum_univ_two, Fin.isValue, Sum.swap_inl,
      Sum.swap_inr, diracMassShellCoeff, diracEpsilon_inl_inl, diracEpsilon_inr_inr,
      diracEpsilon_inl_inr, diracEpsilon_inr_inl, diracSlashCoeff_inl_inl,
      diracSlashCoeff_inr_inr, diracSlashCoeff_inl_inr, diracSlashCoeff_inr_inl,
      weylEpsilon_zero_zero, weylEpsilon_zero_one, weylEpsilon_one_zero,
      weylEpsilon_one_one, vec_to_spinor_apply_00, vec_to_spinor_apply_01,
      vec_to_spinor_apply_10, vec_to_spinor_apply_11]
    ring
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [pow_succ, Complex.I_sq]
    ring
  have hI4 : Complex.I ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, Complex.I_sq]
    ring
  have h_sos :
      ((q 0 : ℂ) + (q 3 : ℂ)) * Q =
        ((Complex.normSq A₀ + Complex.normSq A₁ : ℝ) : ℂ) := by
    push_cast
    rw [← Complex.mul_conj A₀, ← Complex.mul_conj A₁, hQ_expand]
    dsimp [A₀, A₁]
    simp only [map_sub, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring_nf
    simp only [Complex.I_sq, hI3, hI4, h_msq]
    ring
  have h_pos_scale : 0 < q 0 + q 3 := massShellEnergy_add_third_pos hm p
  have h_rhs_nn : 0 ≤ Complex.normSq A₀ + Complex.normSq A₁ :=
    add_nonneg (Complex.normSq_nonneg A₀) (Complex.normSq_nonneg A₁)
  have hQ_eq : Q =
      (((q 0 + q 3)⁻¹ * (Complex.normSq A₀ + Complex.normSq A₁) : ℝ) : ℂ) := by
    have h_ne : (q 0 : ℂ) + (q 3 : ℂ) ≠ 0 := by
      have h_ne_r : ((q 0 + q 3 : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr h_pos_scale.ne'
      simpa using h_ne_r
    apply mul_left_cancel₀ h_ne
    rw [h_sos]
    have h_cast : (((q 0 + q 3)⁻¹ * (Complex.normSq A₀ + Complex.normSq A₁) : ℝ) : ℂ) =
        ((q 0 : ℂ) + (q 3 : ℂ))⁻¹ *
          ((Complex.normSq A₀ + Complex.normSq A₁ : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [h_cast, mul_inv_cancel_left₀ h_ne]
  change 0 ≤ Q
  rw [hQ_eq]
  have h_final : 0 ≤ (q 0 + q 3)⁻¹ * (Complex.normSq A₀ + Complex.normSq A₁) :=
    mul_nonneg (inv_nonneg.mpr h_pos_scale.le) h_rhs_nn
  exact_mod_cast h_final

noncomputable def massiveDiracW (m : ℝ) (hm : 0 < m) :
    WightmanFamily (Fin 2 ⊕ Fin 2) :=
  massShellTwoPointW m (diracMassShellCoeff m) (diracMassShellCoeff_data hm)

noncomputable def massiveDiracTubeExtension (m : ℝ) (hm : 0 < m) :
    TubeExtension (massiveDiracW m hm) :=
  massShellTwoPointTubeExtension m hm (diracMassShellCoeff m)
    (diracMassShellCoeff_data hm)

noncomputable def massiveDiracS (m : ℝ) (hm : 0 < m) :
    SchwingerFamily (Fin 2 ⊕ Fin 2) :=
  massShellTwoPointS m hm (diracMassShellCoeff m) (diracMassShellCoeff_data hm)

theorem massiveDirac_forwardConeSpectrumCondition {m : ℝ} (hm : 0 < m) :
    ForwardConeSpectrumCondition (massiveDiracW m hm) :=
  massShellTwoPoint_forwardConeSpectrumCondition hm (diracMassShellCoeff_data hm)

theorem massiveDiracS_vacuumNormalized {m : ℝ} (hm : 0 < m) :
    OSVacuumNormalized (massiveDiracS m hm) :=
  massShellTwoPointS_vacuumNormalized m hm (diracMassShellCoeff m)
    (diracMassShellCoeff_data hm)

theorem massiveDiracTubeTranslationInvariant {m : ℝ} (hm : 0 < m) :
    TubeTranslationInvariant (massiveDiracTubeExtension m hm) :=
  massShellTwoPointTubeTranslationInvariant hm (diracMassShellCoeff_data hm)

theorem massiveDiracOSTranslationInvariant {m : ℝ} (hm : 0 < m) :
    OSTranslationInvariant (massiveDiracS m hm) :=
  massShellTwoPointOSTranslationInvariant hm (diracMassShellCoeff_data hm)

theorem massiveDiracTubeCovariant {m : ℝ} (hm : 0 < m) :
    TubeCovariant diracRep (massiveDiracTubeExtension m hm) :=
  massShellTwoPointTubeCovariant diracRep hm (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_lorentz m)

theorem massiveDiracPoincareCovariant {m : ℝ} (hm : 0 < m) :
    PoincareCovariant diracRep (massiveDiracW m hm) :=
  massShellTwoPointPoincareCovariant diracRep hm (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_lorentz m)

theorem massiveDiracTubeWickHermiticity {m : ℝ} (hm : 0 < m) :
    TubeWickHermiticity diracStarStructure (massiveDiracTubeExtension m hm) :=
  massShellTwoPointTubeWickHermiticity diracStarStructure hm
    (diracMassShellCoeff_data hm) (diracMassShellCoeff_herm m)

theorem massiveDiracOSHermiticity {m : ℝ} (hm : 0 < m) :
    OSHermiticity diracStarStructure (massiveDiracS m hm) :=
  massShellTwoPointOSHermiticity diracStarStructure hm
    (diracMassShellCoeff_data hm) (diracMassShellCoeff_herm m)

theorem massiveDiracTubePCT {m : ℝ} (hm : 0 < m) :
    TubePCT (-1) diracRep (massiveDiracTubeExtension m hm) :=
  massShellTwoPointTubePCT diracRep hm (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_pct m)

theorem massiveDiracWightmanPCT {m : ℝ} (hm : 0 < m) :
    WightmanPCT (-1) diracRep (massiveDiracW m hm) :=
  massShellTwoPointWightmanPCT diracRep hm (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_pct m)

theorem massiveDiracWeakLocality {m : ℝ} (hm : 0 < m) :
    WeakLocality (-1) (massiveDiracW m hm) :=
  massShellTwoPointWeakLocality diracRep hm
    (diracMassShellCoeff_data hm) (diracMassShellCoeff_lorentz m)
    (diracMassShellCoeff_pct m)

def finOneFunEquiv (α : Type*) : (Fin 1 → α) ≃ α where
  toFun f := f 0
  invFun a _ := a
  left_inv f := by
    ext i
    fin_cases i
    rfl
  right_inv _ := rfl

lemma sum_fin_one_fun {κ : Type*} [Fintype κ] (G : (Fin 1 → κ) → ℂ) :
    (∑ α : Fin 1 → κ, G α) = ∑ a : κ, G (fun _ => a) :=
  ((finOneFunEquiv κ).symm.sum_comp G).symm

lemma sum_prod_diracStarStructure_C_mul (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2)
    (K : (Fin n → Fin 2 ⊕ Fin 2) → ℂ) :
    (∑ β : Fin n → Fin 2 ⊕ Fin 2,
      (∏ i : Fin n, diracStarStructure.C (α i) (β i)) * K β) =
      K (Sum.swap ∘ α) := by
  dsimp [diracStarStructure]
  exact sum_prod_chiralDoubleStarStructure_C_mul leftWeylRep leftWeylRep_hasRealConj n α K

theorem massiveDiracOneParticlePositivity {m : ℝ} (hm : 0 < m) :
    OneParticlePositivity diracStarStructure (massiveDiracW m hm) := by
  intro N hN F G hG
  have h_zero_term :
      0 ≤ ∑ α : Fin 0 → Fin 2 ⊕ Fin 2, ∑ α' : Fin 0 → Fin 2 ⊕ Fin 2,
        ∑ β : Fin 0 → Fin 2 ⊕ Fin 2,
          (∏ i, diracStarStructure.C (α i) (β i)) *
            massiveDiracW m hm 0 (Fin.append (β ∘ Fin.rev) α') (G 0 0 α α') := by
    simp only [Fintype.sum_unique, massiveDiracW, massShellTwoPointW_zero_apply,
      Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    have hL0 : (fun i : Fin 0 => (0 : Fin 0 → Fin 4 → ℝ) (Fin.castAdd 0 (Fin.rev i))) = 0 :=
      Subsingleton.elim _ _
    have hR0 : (fun i : Fin 0 => (0 : Fin 0 → Fin 4 → ℝ) (Fin.natAdd 0 i)) = 0 :=
      Subsingleton.elim _ _
    rw [hG, hL0, hR0, mul_comm, Complex.mul_conj]
    exact_mod_cast Complex.normSq_nonneg _
  interval_cases N
  · simpa [Finset.range_one] using h_zero_term
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have h01 :
        (∑ α : Fin 0 → Fin 2 ⊕ Fin 2, ∑ α' : Fin 1 → Fin 2 ⊕ Fin 2,
          ∑ β : Fin 0 → Fin 2 ⊕ Fin 2,
            (∏ i, diracStarStructure.C (α i) (β i)) *
              massiveDiracW m hm 1 (Fin.append (β ∘ Fin.rev) α') (G 0 1 α α')) = 0 := by
      simp [massiveDiracW]
    have h10 :
        (∑ α : Fin 1 → Fin 2 ⊕ Fin 2, ∑ α' : Fin 0 → Fin 2 ⊕ Fin 2,
          ∑ β : Fin 1 → Fin 2 ⊕ Fin 2,
            (∏ i, diracStarStructure.C (α i) (β i)) *
              massiveDiracW m hm 1 (Fin.append (β ∘ Fin.rev) α') (G 1 0 α α')) = 0 := by
      simp [massiveDiracW]
    have h11 :
        0 ≤ ∑ α : Fin 1 → Fin 2 ⊕ Fin 2, ∑ α' : Fin 1 → Fin 2 ⊕ Fin 2,
          ∑ β : Fin 1 → Fin 2 ⊕ Fin 2,
            (∏ i, diracStarStructure.C (α i) (β i)) *
              massiveDiracW m hm 2 (Fin.append (β ∘ Fin.rev) α') (G 1 1 α α') := by
      have h_sum_β : ∀ (α α' : Fin 1 → Fin 2 ⊕ Fin 2),
          (∑ β : Fin 1 → Fin 2 ⊕ Fin 2,
            (∏ i, diracStarStructure.C (α i) (β i)) *
              massiveDiracW m hm 2 (Fin.append (β ∘ Fin.rev) α') (G 1 1 α α')) =
          massiveDiracW m hm 2
            (Fin.append ((Sum.swap ∘ α) ∘ Fin.rev) α') (G 1 1 α α') :=
        fun α α' => sum_prod_diracStarStructure_C_mul 1 α _
      simp_rw [h_sum_β]
      rw [sum_fin_one_fun]
      simp_rw [sum_fin_one_fun]
      have h_app : ∀ γ γ' : Fin 2 ⊕ Fin 2,
          Fin.append (((Sum.swap ∘ fun _ : Fin 1 => γ) ∘ Fin.rev)) (fun _ : Fin 1 => γ') =
            ![Sum.swap γ, γ'] := by
        intro γ γ'
        ext i
        fin_cases i <;> rfl
      simp_rw [h_app, massiveDiracW, massShellTwoPointW_two_apply]
      have h_swap_sum :
          (∑ γ : Fin 2 ⊕ Fin 2, ∑ γ' : Fin 2 ⊕ Fin 2,
            ∫ p : Fin 3 → ℝ,
              massShellWeight m (diracMassShellCoeff m) ![Sum.swap γ, γ'] p *
                minkowskiFourier (G 1 1 (fun _ => γ) (fun _ => γ'))
                  (twoPointMomentum (massShellVec m p))) =
          ∫ p : Fin 3 → ℝ, ∑ γ : Fin 2 ⊕ Fin 2, ∑ γ' : Fin 2 ⊕ Fin 2,
            massShellWeight m (diracMassShellCoeff m) ![Sum.swap γ, γ'] p *
              minkowskiFourier (G 1 1 (fun _ => γ) (fun _ => γ'))
                (twoPointMomentum (massShellVec m p)) := by
        have h_in : ∀ γ : Fin 2 ⊕ Fin 2,
            (∑ γ' : Fin 2 ⊕ Fin 2,
              ∫ p : Fin 3 → ℝ,
                massShellWeight m (diracMassShellCoeff m) ![Sum.swap γ, γ'] p *
                  minkowskiFourier (G 1 1 (fun _ => γ) (fun _ => γ'))
                    (twoPointMomentum (massShellVec m p))) =
            ∫ p : Fin 3 → ℝ, ∑ γ' : Fin 2 ⊕ Fin 2,
              massShellWeight m (diracMassShellCoeff m) ![Sum.swap γ, γ'] p *
                minkowskiFourier (G 1 1 (fun _ => γ) (fun _ => γ'))
                  (twoPointMomentum (massShellVec m p)) :=
          fun γ => (integral_finsetSum Finset.univ (fun γ' _ =>
            integrable_massShellWeight_mul_minkowskiFourier
              (diracMassShellCoeff_data hm) ![Sum.swap γ, γ']
              (G 1 1 (fun _ => γ) (fun _ => γ')))).symm
        rw [Finset.sum_congr rfl (fun γ _ => h_in γ),
            ← integral_finsetSum Finset.univ (fun γ _ =>
              integrable_finsetSum Finset.univ (fun γ' _ =>
                integrable_massShellWeight_mul_minkowskiFourier
                  (diracMassShellCoeff_data hm) ![Sum.swap γ, γ']
                  (G 1 1 (fun _ => γ) (fun _ => γ'))))]
      rw [h_swap_sum]
      refine complex_integral_nonneg
        (integrable_finsetSum Finset.univ (fun γ _ =>
          integrable_finsetSum Finset.univ (fun γ' _ =>
            integrable_massShellWeight_mul_minkowskiFourier
              (diracMassShellCoeff_data hm) ![Sum.swap γ, γ']
              (G 1 1 (fun _ => γ) (fun _ => γ')))))
        (fun p => ?_)
      dsimp only [massShellWeight]
      have h_factor :
          (∑ γ : Fin 2 ⊕ Fin 2, ∑ γ' : Fin 2 ⊕ Fin 2,
            (((2 * massShellEnergy m p)⁻¹ : ℂ) *
              diracMassShellCoeff m ![Sum.swap γ, γ'] (massShellVec m p)) *
              minkowskiFourier (G 1 1 (fun _ => γ) (fun _ => γ'))
                (twoPointMomentum (massShellVec m p))) =
          ((2 * massShellEnergy m p)⁻¹ : ℂ) *
            ∑ γ : Fin 2 ⊕ Fin 2, ∑ γ' : Fin 2 ⊕ Fin 2,
              (starRingEnd ℂ)
                (minkowskiFourier (F 1 (fun _ => γ)) (fun _ => -massShellVec m p)) *
                diracMassShellCoeff m ![Sum.swap γ, γ'] (massShellVec m p) *
                minkowskiFourier (F 1 (fun _ => γ')) (fun _ => -massShellVec m p) := by
        simp_rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun γ _ => Finset.sum_congr rfl (fun γ' _ => ?_))
        rw [minkowskiFourier_split_one_one_twoPointMomentum (massShellVec m p)
          (F 1 (fun _ => γ)) (F 1 (fun _ => γ'))
          (G 1 1 (fun _ => γ) (fun _ => γ'))
          (hG 1 1 (fun _ => γ) (fun _ => γ'))]
        ring
      rw [h_factor]
      have h_inv_nn : (0 : ℂ) ≤ ((2 * massShellEnergy m p)⁻¹ : ℂ) := by
        have h_real : 0 ≤ (2 * massShellEnergy m p)⁻¹ :=
          inv_nonneg.mpr (mul_pos zero_lt_two (massShellEnergy_pos hm p)).le
        exact_mod_cast h_real
      exact mul_nonneg h_inv_nn (diracMassShellCoeff_quad_nonneg hm p
        (fun γ => minkowskiFourier (F 1 (fun _ => γ)) (fun _ => -massShellVec m p)))
    rw [h01, h10, add_zero]
    exact add_nonneg h_zero_term (add_nonneg le_rfl h11)

theorem massiveDiracW_twoPoint_inl_inr_zero_ne_zero {m : ℝ} (hm : 0 < m) :
    massiveDiracW m hm 2 ![Sum.inl 0, Sum.inr 0] ≠ 0 := by
  refine (massShellTwoPoint_nondeg_and_not_zeroMomentum hm
    (diracMassShellCoeff_data hm) ![Sum.inl 0, Sum.inr 0]
    ((continuous_massShellEnergy m).add (continuous_apply 2))
    (massShellEnergy_add_third_pos hm) (fun p => ?_)).1
  simp [diracMassShellCoeff, massShellVec]

theorem massiveDiracW_twoPoint_nondegenerate {m : ℝ} (hm : 0 < m) :
    ∃ β : Fin 2 → Fin 2 ⊕ Fin 2, massiveDiracW m hm 2 β ≠ 0 :=
  ⟨![Sum.inl 0, Sum.inr 0], massiveDiracW_twoPoint_inl_inr_zero_ne_zero hm⟩

theorem not_zeroMomentumSpectrumCondition_massiveDiracW {m : ℝ} (hm : 0 < m) :
    ¬ ZeroMomentumSpectrumCondition (massiveDiracW m hm) := by
  refine (massShellTwoPoint_nondeg_and_not_zeroMomentum hm
    (diracMassShellCoeff_data hm) ![Sum.inl 0, Sum.inr 0]
    ((continuous_massShellEnergy m).add (continuous_apply 2))
    (massShellEnergy_add_third_pos hm) (fun p => ?_)).2
  simp [diracMassShellCoeff, massShellVec]

theorem massiveDirac_spin_statistics {m : ℝ} (hm : 0 < m) {η : ℂ}
    (hloc : WeakLocality η (massiveDiracW m hm)) :
    η = -1 :=
  spin_statistics_of_tubePCT_and_weakLocality diracRep (massiveDiracW m hm)
    (massiveDiracTubeExtension m hm) (massiveDiracTubeCovariant hm)
    (massiveDiracTubePCT hm) hloc (massiveDiracW_twoPoint_nondegenerate hm)

theorem not_bosonic_weakLocality_massiveDiracW {m : ℝ} (hm : 0 < m) :
    ¬ WeakLocality 1 (massiveDiracW m hm) := by
  intro hbos
  have h := massiveDirac_spin_statistics hm hbos
  norm_num at h

theorem massiveDirac_master {m : ℝ} (hm : 0 < m) :
    ForwardConeSpectrumCondition (massiveDiracW m hm) ∧
    ¬ ZeroMomentumSpectrumCondition (massiveDiracW m hm) ∧
    (∃ β : Fin 2 → Fin 2 ⊕ Fin 2, massiveDiracW m hm 2 β ≠ 0) ∧
    PoincareCovariant diracRep (massiveDiracW m hm) ∧
    TubeCovariant diracRep (massiveDiracTubeExtension m hm) ∧
    TubeTranslationInvariant (massiveDiracTubeExtension m hm) ∧
    TubeWickHermiticity diracStarStructure (massiveDiracTubeExtension m hm) ∧
    TubePCT (-1) diracRep (massiveDiracTubeExtension m hm) ∧
    WightmanPCT (-1) diracRep (massiveDiracW m hm) ∧
    WeakLocality (-1) (massiveDiracW m hm) ∧
    OneParticlePositivity diracStarStructure (massiveDiracW m hm) ∧
    (∀ η : ℂ, WeakLocality η (massiveDiracW m hm) → η = -1) :=
  ⟨massiveDirac_forwardConeSpectrumCondition hm,
   not_zeroMomentumSpectrumCondition_massiveDiracW hm,
   massiveDiracW_twoPoint_nondegenerate hm,
   massiveDiracPoincareCovariant hm,
   massiveDiracTubeCovariant hm,
   massiveDiracTubeTranslationInvariant hm,
   massiveDiracTubeWickHermiticity hm,
   massiveDiracTubePCT hm,
   massiveDiracWightmanPCT hm,
   massiveDiracWeakLocality hm,
   massiveDiracOneParticlePositivity hm,
   fun _ hloc => massiveDirac_spin_statistics hm hloc⟩

end
end QFT
