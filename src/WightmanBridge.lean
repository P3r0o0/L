import VacuumTheory

namespace QFT

open Geometry Geometry.MatrixAnalysis Geometry.PolarDecomposition
  MeasureTheory Filter Topology Matrix
open scoped ComplexOrder FourierTransform RealInnerProductSpace
  Interval ContDiff InnerProductSpace

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def compactSchwartzZero (n : ℕ) : CompactSchwartz n :=
  ⟨0, HasCompactSupport.zero⟩

def compactSchwartzAdd (n : ℕ) (f g : CompactSchwartz n) : CompactSchwartz n :=
  ⟨f.val + g.val, f.property.add g.property⟩

def compactSchwartzSMul (n : ℕ) (c : ℂ) (f : CompactSchwartz n) : CompactSchwartz n :=
  ⟨c • f.val, f.property.smul_left⟩

@[simp]
lemma compactSchwartzZero_val (n : ℕ) :
    (compactSchwartzZero n).val = 0 := rfl

@[simp]
lemma compactSchwartzAdd_val (n : ℕ) (f g : CompactSchwartz n) :
    (compactSchwartzAdd n f g).val = f.val + g.val := rfl

@[simp]
lemma compactSchwartzSMul_val (n : ℕ) (c : ℂ) (f : CompactSchwartz n) :
    (compactSchwartzSMul n c f).val = c • f.val := rfl

lemma hasCompactSupport_sum_compactSchwartz {α : Type*} (n : ℕ)
    (s : Finset α) (f : α → CompactSchwartz n) :
    HasCompactSupport ((∑ a ∈ s, (f a).val : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
      (Fin n → Fin 4 → ℝ) → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact HasCompactSupport.zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (f a).property.add ih

def compactSchwartzSum {α : Type*} (n : ℕ)
    (s : Finset α) (f : α → CompactSchwartz n) : CompactSchwartz n :=
  ⟨∑ a ∈ s, (f a).val, hasCompactSupport_sum_compactSchwartz n s f⟩

@[simp]
lemma compactSchwartzSum_val {α : Type*} (n : ℕ)
    (s : Finset α) (f : α → CompactSchwartz n) :
    (compactSchwartzSum n s f).val = ∑ a ∈ s, (f a).val := rfl

lemma schwartzMap_sum_apply {α : Type*} (n : ℕ)
    (s : Finset α) (f : α → SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (x : Fin n → Fin 4 → ℝ) :
    (∑ a ∈ s, f a) x = ∑ a ∈ s, f a x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    rfl
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

@[simp]
lemma wightmanConcatSchwartz_zero_left (j k : ℕ) (g : CompactSchwartz k) :
    wightmanConcatSchwartz j k (compactSchwartzZero j) g = 0 := by
  ext x
  simp [wightmanConcatSchwartz_apply]

@[simp]
lemma wightmanConcatSchwartz_zero_right (j k : ℕ) (f : CompactSchwartz j) :
    wightmanConcatSchwartz j k f (compactSchwartzZero k) = 0 := by
  ext x
  simp [wightmanConcatSchwartz_apply]

lemma wightmanConcatSchwartz_add_left (j k : ℕ)
    (f₁ f₂ : CompactSchwartz j) (g : CompactSchwartz k) :
    wightmanConcatSchwartz j k (compactSchwartzAdd j f₁ f₂) g =
      wightmanConcatSchwartz j k f₁ g + wightmanConcatSchwartz j k f₂ g := by
  ext x
  change (starRingEnd ℂ)
      ((f₁.val (fun i => x (Fin.castAdd k (Fin.rev i))) +
        f₂.val (fun i => x (Fin.castAdd k (Fin.rev i))))) *
      g.val (fun i => x (Fin.natAdd j i)) =
    wightmanConcatSchwartz j k f₁ g x + wightmanConcatSchwartz j k f₂ g x
  rw [map_add, add_mul]
  rfl

lemma wightmanConcatSchwartz_add_right (j k : ℕ)
    (f : CompactSchwartz j) (g₁ g₂ : CompactSchwartz k) :
    wightmanConcatSchwartz j k f (compactSchwartzAdd k g₁ g₂) =
      wightmanConcatSchwartz j k f g₁ + wightmanConcatSchwartz j k f g₂ := by
  ext x
  change (starRingEnd ℂ) (f.val (fun i => x (Fin.castAdd k (Fin.rev i)))) *
      (g₁.val (fun i => x (Fin.natAdd j i)) + g₂.val (fun i => x (Fin.natAdd j i))) =
    wightmanConcatSchwartz j k f g₁ x + wightmanConcatSchwartz j k f g₂ x
  rw [mul_add]
  rfl

lemma wightmanConcatSchwartz_smul_left (j k : ℕ) (c : ℂ)
    (f : CompactSchwartz j) (g : CompactSchwartz k) :
    wightmanConcatSchwartz j k (compactSchwartzSMul j c f) g =
      star c • wightmanConcatSchwartz j k f g := by
  ext x
  change (starRingEnd ℂ) (c * f.val (fun i => x (Fin.castAdd k (Fin.rev i)))) *
      g.val (fun i => x (Fin.natAdd j i)) =
    star c * wightmanConcatSchwartz j k f g x
  rw [map_mul, ← Complex.star_def, mul_assoc]
  rfl

lemma wightmanConcatSchwartz_smul_right (j k : ℕ) (c : ℂ)
    (f : CompactSchwartz j) (g : CompactSchwartz k) :
    wightmanConcatSchwartz j k f (compactSchwartzSMul k c g) =
      c • wightmanConcatSchwartz j k f g := by
  ext x
  change (starRingEnd ℂ) (f.val (fun i => x (Fin.castAdd k (Fin.rev i)))) *
      (c * g.val (fun i => x (Fin.natAdd j i))) =
    c * wightmanConcatSchwartz j k f g x
  rw [mul_left_comm]
  rfl

lemma wightmanConcatSchwartz_smul_smul (j k : ℕ) (cA cB : ℂ)
    (f : CompactSchwartz j) (g : CompactSchwartz k) :
    wightmanConcatSchwartz j k (compactSchwartzSMul j cA f) (compactSchwartzSMul k cB g) =
      (star cA * cB) • wightmanConcatSchwartz j k f g := by
  rw [wightmanConcatSchwartz_smul_left, wightmanConcatSchwartz_smul_right, smul_smul]

lemma wightmanConcatSchwartz_sum_sum {α β : Type*}
    (j k : ℕ) (s : Finset α) (t : Finset β)
    (f : α → CompactSchwartz j) (g : β → CompactSchwartz k) :
    wightmanConcatSchwartz j k (compactSchwartzSum j s f) (compactSchwartzSum k t g) =
      ∑ a ∈ s, ∑ b ∈ t, wightmanConcatSchwartz j k (f a) (g b) := by
  ext x
  rw [wightmanConcatSchwartz_apply, compactSchwartzSum_val, compactSchwartzSum_val,
      schwartzMap_sum_apply, schwartzMap_sum_apply,
      schwartzMap_sum_apply, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [schwartzMap_sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rfl

lemma sum_comm_finset_double {γ δ₁ δ₂ : Type*} (u : Finset γ) (s : Finset δ₁) (t : Finset δ₂)
    (f : γ → δ₁ → δ₂ → ℂ) :
    (∑ x ∈ u, ∑ a ∈ s, ∑ b ∈ t, f x a b) =
      ∑ a ∈ s, ∑ b ∈ t, ∑ x ∈ u, f x a b := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_comm)

def wightmanSingleDelta (A : WightmanConfig ι) (c : ℂ)
    (j : ℕ) (α : Fin j → ι) : CompactSchwartz j :=
  if h : j = A.1 then
    if h ▸ α = A.2.1 then
      h ▸ compactSchwartzSMul A.1 c A.2.2
    else
      compactSchwartzZero j
  else
    compactSchwartzZero j

omit [Fintype ι] in
@[simp]
lemma wightmanSingleDelta_eq_deg (j : ℕ) (α₀ α : Fin j → ι)
    (f₀ : CompactSchwartz j) (c : ℂ) :
    wightmanSingleDelta ⟨j, (α₀, f₀)⟩ c j α =
      if α = α₀ then compactSchwartzSMul j c f₀ else compactSchwartzZero j := by
  simp [wightmanSingleDelta]

omit [Fintype ι] in
lemma wightmanSingleDelta_ne_deg (A : WightmanConfig ι) (c : ℂ) {j : ℕ}
    (hj : j ≠ A.1) (α : Fin j → ι) :
    wightmanSingleDelta A c j α = compactSchwartzZero j := by
  simp [wightmanSingleDelta, hj]

lemma wightmanKernel_mk
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    (j k : ℕ) (α : Fin j → ι) (α' : Fin k → ι)
    (f : CompactSchwartz j) (g : CompactSchwartz k) :
    wightmanKernel S W ⟨j, (α, f)⟩ ⟨k, (α', g)⟩ =
      ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α')
            (wightmanConcatSchwartz j k f g) := rfl

lemma inner_sum_wightmanSingleDelta
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    (A B : WightmanConfig ι) (cA cB : ℂ) (j k : ℕ) :
    (∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
      (∏ i : Fin j, S.C (α i) (β i)) *
        W (j + k) (Fin.append (β ∘ Fin.rev) α')
          (wightmanConcatSchwartz j k
            (wightmanSingleDelta A cA j α)
            (wightmanSingleDelta B cB k α'))) =
      if j = A.1 then
        if k = B.1 then
          star cA * cB * wightmanKernel S W A B
        else 0
      else 0 := by
  rcases A with ⟨j₀, α₀, f₀⟩
  rcases B with ⟨k₀, α₀', g₀⟩
  change (∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
      (∏ i : Fin j, S.C (α i) (β i)) *
        W (j + k) (Fin.append (β ∘ Fin.rev) α')
          (wightmanConcatSchwartz j k
            (wightmanSingleDelta ⟨j₀, (α₀, f₀)⟩ cA j α)
            (wightmanSingleDelta ⟨k₀, (α₀', g₀)⟩ cB k α'))) =
      if j = j₀ then
        if k = k₀ then
          star cA * cB * wightmanKernel S W ⟨j₀, (α₀, f₀)⟩ ⟨k₀, (α₀', g₀)⟩
        else 0
      else 0
  by_cases hj : j = j₀
  · subst hj
    rw [if_pos rfl]
    by_cases hk : k = k₀
    · subst hk
      rw [if_pos rfl]
      have h_term : ∀ (α : Fin j → ι) (α' : Fin k → ι),
          (∑ β : Fin j → ι,
            (∏ i : Fin j, S.C (α i) (β i)) *
              W (j + k) (Fin.append (β ∘ Fin.rev) α')
                (wightmanConcatSchwartz j k
                  (wightmanSingleDelta ⟨j, (α₀, f₀)⟩ cA j α)
                  (wightmanSingleDelta ⟨k, (α₀', g₀)⟩ cB k α'))) =
            if α = α₀ then
              if α' = α₀' then
                star cA * cB * wightmanKernel S W ⟨j, (α₀, f₀)⟩ ⟨k, (α₀', g₀)⟩
              else 0
            else 0 := by
        intro α α'
        rw [wightmanSingleDelta_eq_deg, wightmanSingleDelta_eq_deg]
        by_cases hα : α = α₀
        · subst hα
          rw [if_pos rfl]
          by_cases hα' : α' = α₀'
          · subst hα'
            rw [if_pos rfl, if_pos rfl, if_pos rfl, wightmanKernel_mk, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun β _ => ?_)
            rw [wightmanConcatSchwartz_smul_smul, map_smul, smul_eq_mul]
            ring
          · rw [if_neg hα', if_pos rfl, if_neg hα']
            refine Finset.sum_eq_zero (fun β _ => ?_)
            rw [wightmanConcatSchwartz_zero_right, map_zero, mul_zero]
        · rw [if_neg hα, if_neg hα]
          refine Finset.sum_eq_zero (fun β _ => ?_)
          rw [wightmanConcatSchwartz_zero_left, map_zero, mul_zero]
      simp_rw [h_term]
      have h_sum_k : ∀ α : Fin j → ι,
          (∑ α' : Fin k → ι,
            if α = α₀ then
              if α' = α₀' then
                star cA * cB * wightmanKernel S W ⟨j, (α₀, f₀)⟩ ⟨k, (α₀', g₀)⟩
              else 0
            else 0) =
          if α = α₀ then
            star cA * cB * wightmanKernel S W ⟨j, (α₀, f₀)⟩ ⟨k, (α₀', g₀)⟩
          else 0 := by
        intro α
        by_cases hα : α = α₀ <;> simp [hα]
      simp_rw [h_sum_k]
      simp
    · rw [if_neg hk]
      refine Finset.sum_eq_zero (fun α _ => Finset.sum_eq_zero (fun α' _ => ?_))
      refine Finset.sum_eq_zero (fun β _ => ?_)
      rw [wightmanSingleDelta_ne_deg ⟨k₀, (α₀', g₀)⟩ cB hk,
          wightmanConcatSchwartz_zero_right, map_zero, mul_zero]
  · rw [if_neg hj]
    refine Finset.sum_eq_zero (fun α _ => Finset.sum_eq_zero (fun α' _ => ?_))
    refine Finset.sum_eq_zero (fun β _ => ?_)
    rw [wightmanSingleDelta_ne_deg ⟨j₀, (α₀, f₀)⟩ cA hj,
        wightmanConcatSchwartz_zero_left, map_zero, mul_zero]

lemma sum_range_ite_ite
    {N j₀ k₀ : ℕ} (hj : j₀ ≤ N) (hk : k₀ ≤ N) (v : ℂ) :
    (∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      if j = j₀ then if k = k₀ then v else 0 else 0) = v := by
  have h_sum_k : ∀ j : ℕ,
      (∑ k ∈ Finset.range (N + 1),
        if j = j₀ then if k = k₀ then v else 0 else 0) =
      if j = j₀ then v else 0 := by
    intro j
    by_cases hj' : j = j₀
    · rw [if_pos hj']
      simp_rw [if_pos hj']
      rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
    · rw [if_neg hj']
      simp_rw [if_neg hj']
      exact Finset.sum_const_zero
  simp_rw [h_sum_k]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]

theorem sum_wightmanSingleDelta_borchers
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    {N : ℕ} {A B : WightmanConfig ι} (hA : A.1 ≤ N) (hB : B.1 ≤ N) (cA cB : ℂ) :
    (∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α')
            (wightmanConcatSchwartz j k
              (wightmanSingleDelta A cA j α)
              (wightmanSingleDelta B cB k α'))) =
      star cA * cB * wightmanKernel S W A B := by
  simp_rw [inner_sum_wightmanSingleDelta]
  exact sum_range_ite_ite hA hB (star cA * cB * wightmanKernel S W A B)

def wightmanCollapsedCompact (Ψ : WightmanConfig ι →₀ ℂ)
    (j : ℕ) (α : Fin j → ι) : CompactSchwartz j :=
  compactSchwartzSum j Ψ.support (fun A => wightmanSingleDelta A (Ψ A) j α)

def wightmanCollapsedSchwartz (Ψ : WightmanConfig ι →₀ ℂ)
    (j : ℕ) (α : Fin j → ι) : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ :=
  (wightmanCollapsedCompact Ψ j α).val

def wightmanSupportMaxDeg (Ψ : WightmanConfig ι →₀ ℂ) : ℕ :=
  Ψ.support.sup Sigma.fst

omit [Fintype ι] [DecidableEq ι] in
lemma deg_le_wightmanSupportMaxDeg {Ψ : WightmanConfig ι →₀ ℂ} {A : WightmanConfig ι}
    (hA : A ∈ Ψ.support) :
    A.1 ≤ wightmanSupportMaxDeg Ψ :=
  Finset.le_sup (f := Sigma.fst) hA

lemma inner_sum_wightmanCollapsedCompact
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    (Ψ Φ : WightmanConfig ι →₀ ℂ) (j k : ℕ) :
    (∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
      (∏ i : Fin j, S.C (α i) (β i)) *
        W (j + k) (Fin.append (β ∘ Fin.rev) α')
          (wightmanConcatSchwartz j k
            (wightmanCollapsedCompact Ψ j α)
            (wightmanCollapsedCompact Φ k α'))) =
      ∑ A ∈ Ψ.support, ∑ B ∈ Φ.support,
        if j = A.1 then
          if k = B.1 then
            star (Ψ A) * Φ B * wightmanKernel S W A B
          else 0
        else 0 := by
  have h_expand : ∀ (α : Fin j → ι) (α' : Fin k → ι) (β : Fin j → ι),
      (∏ i : Fin j, S.C (α i) (β i)) *
        W (j + k) (Fin.append (β ∘ Fin.rev) α')
          (wightmanConcatSchwartz j k
            (wightmanCollapsedCompact Ψ j α)
            (wightmanCollapsedCompact Φ k α')) =
      ∑ A ∈ Ψ.support, ∑ B ∈ Φ.support,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α')
            (wightmanConcatSchwartz j k
              (wightmanSingleDelta A (Ψ A) j α)
              (wightmanSingleDelta B (Φ B) k α')) := by
    intro α α' β
    unfold wightmanCollapsedCompact
    rw [wightmanConcatSchwartz_sum_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    rw [map_sum, Finset.mul_sum]
  simp_rw [h_expand]
  have h_comm_β : ∀ (α : Fin j → ι) (α' : Fin k → ι),
      (∑ β : Fin j → ι, ∑ A ∈ Ψ.support, ∑ B ∈ Φ.support,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α')
            (wightmanConcatSchwartz j k
              (wightmanSingleDelta A (Ψ A) j α)
              (wightmanSingleDelta B (Φ B) k α'))) =
      ∑ A ∈ Ψ.support, ∑ B ∈ Φ.support, ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α')
            (wightmanConcatSchwartz j k
              (wightmanSingleDelta A (Ψ A) j α)
              (wightmanSingleDelta B (Φ B) k α')) :=
    fun _ _ => sum_comm_finset_double _ _ _ _
  simp_rw [h_comm_β]
  have h_comm_α' : ∀ (α : Fin j → ι),
      (∑ α' : Fin k → ι, ∑ A ∈ Ψ.support, ∑ B ∈ Φ.support, ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α')
            (wightmanConcatSchwartz j k
              (wightmanSingleDelta A (Ψ A) j α)
              (wightmanSingleDelta B (Φ B) k α'))) =
      ∑ A ∈ Ψ.support, ∑ B ∈ Φ.support, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α')
            (wightmanConcatSchwartz j k
              (wightmanSingleDelta A (Ψ A) j α)
              (wightmanSingleDelta B (Φ B) k α')) :=
    fun _ => sum_comm_finset_double _ _ _ _
  simp_rw [h_comm_α']
  rw [sum_comm_finset_double]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  refine Finset.sum_congr rfl (fun B _ => ?_)
  exact inner_sum_wightmanSingleDelta S W A B (Ψ A) (Φ B) j k

theorem wightmanPreInner_eq_borchersSum
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    (Ψ Φ : WightmanConfig ι →₀ ℂ) {N : ℕ}
    (hΨ : wightmanSupportMaxDeg Ψ ≤ N) (hΦ : wightmanSupportMaxDeg Φ ≤ N) :
    (∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α')
            (wightmanConcatSchwartz j k
              (wightmanCollapsedCompact Ψ j α)
              (wightmanCollapsedCompact Φ k α'))) =
      wightmanPreInner S W Ψ Φ := by
  simp_rw [inner_sum_wightmanCollapsedCompact]
  have h_comm_k : ∀ j : ℕ,
      (∑ k ∈ Finset.range (N + 1), ∑ A ∈ Ψ.support, ∑ B ∈ Φ.support,
        if j = A.1 then
          if k = B.1 then
            star (Ψ A) * Φ B * wightmanKernel S W A B
          else 0
        else 0) =
      ∑ A ∈ Ψ.support, ∑ B ∈ Φ.support, ∑ k ∈ Finset.range (N + 1),
        if j = A.1 then
          if k = B.1 then
            star (Ψ A) * Φ B * wightmanKernel S W A B
          else 0
        else 0 :=
    fun _ => sum_comm_finset_double _ _ _ _
  simp_rw [h_comm_k]
  rw [sum_comm_finset_double]
  unfold wightmanPreInner Finsupp.sum
  refine Finset.sum_congr rfl (fun A hA => ?_)
  refine Finset.sum_congr rfl (fun B hB => ?_)
  exact sum_range_ite_ite
    ((deg_le_wightmanSupportMaxDeg hA).trans hΨ)
    ((deg_le_wightmanSupportMaxDeg hB).trans hΦ)
    (star (Ψ A) * Φ B * wightmanKernel S W A B)

def CompactPositivity {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) : Prop :=
  ∀ (N : ℕ) (F : ∀ j : ℕ, (Fin j → ι) → CompactSchwartz j),
    0 ≤ ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α')
            (wightmanConcatSchwartz j k (F j α) (F k α'))

theorem compactPositivity_of_positivity
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {W : WightmanFamily ι}
    (hpos : Positivity S W) :
    CompactPositivity S W := by
  intro N F
  exact hpos N (fun j α => (F j α).val)
    (fun j k α α' => wightmanConcatSchwartz j k (F j α) (F k α'))
    (fun _ _ _ _ _ => rfl)

theorem wightmanPreInner_self_nonneg_of_compactPositivity
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {W : WightmanFamily ι}
    (hpos : CompactPositivity S W) (Ψ : WightmanConfig ι →₀ ℂ) :
    0 ≤ wightmanPreInner S W Ψ Ψ := by
  rw [← wightmanPreInner_eq_borchersSum S W Ψ Ψ le_rfl le_rfl]
  exact hpos (wightmanSupportMaxDeg Ψ) (wightmanCollapsedCompact Ψ)

theorem wightmanPreInner_self_nonneg_of_positivity
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {W : WightmanFamily ι}
    (hpos : Positivity S W) (Ψ : WightmanConfig ι →₀ ℂ) :
    0 ≤ wightmanPreInner S W Ψ Ψ :=
  wightmanPreInner_self_nonneg_of_compactPositivity (compactPositivity_of_positivity hpos) Ψ

theorem wightmanKernelPositive_of_compactPositivity
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {W : WightmanFamily ι}
    (hpos : CompactPositivity S W) :
    WightmanKernelPositive S W :=
  fun Ψ => (Complex.nonneg_iff.mp (wightmanPreInner_self_nonneg_of_compactPositivity hpos Ψ)).1

theorem wightmanKernelPositive_of_positivity
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {W : WightmanFamily ι}
    (hpos : Positivity S W) :
    WightmanKernelPositive S W :=
  wightmanKernelPositive_of_compactPositivity (compactPositivity_of_positivity hpos)

theorem star_wightmanPreInner_self_of_compactPositivity
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {W : WightmanFamily ι}
    (hpos : CompactPositivity S W) (Ψ : WightmanConfig ι →₀ ℂ) :
    star (wightmanPreInner S W Ψ Ψ) = wightmanPreInner S W Ψ Ψ := by
  rw [Complex.star_def, Complex.conj_eq_iff_im]
  exact (Complex.nonneg_iff.mp (wightmanPreInner_self_nonneg_of_compactPositivity hpos Ψ)).2.symm

theorem star_wightmanPreInner_self_of_positivity
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {W : WightmanFamily ι}
    (hpos : Positivity S W) (Ψ : WightmanConfig ι →₀ ℂ) :
    star (wightmanPreInner S W Ψ Ψ) = wightmanPreInner S W Ψ Ψ :=
  star_wightmanPreInner_self_of_compactPositivity (compactPositivity_of_positivity hpos) Ψ

@[simp]
lemma wightmanPreInner_zero_left {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) (Φ : WightmanConfig ι →₀ ℂ) :
    wightmanPreInner S W 0 Φ = 0 := by
  simp [wightmanPreInner]

@[simp]
lemma wightmanPreInner_zero_right {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) (Ψ : WightmanConfig ι →₀ ℂ) :
    wightmanPreInner S W Ψ 0 = 0 := by
  simp [wightmanPreInner]

lemma wightmanPreInner_add_left_raw {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) (Ψ₁ Ψ₂ Φ : WightmanConfig ι →₀ ℂ) :
    wightmanPreInner S W (Ψ₁ + Ψ₂) Φ =
      wightmanPreInner S W Ψ₁ Φ + wightmanPreInner S W Ψ₂ Φ := by
  unfold wightmanPreInner
  rw [Finsupp.sum_add_index']
  · intro A
    simp
  · intro A c₁ c₂
    simp [add_mul, Finsupp.sum_add]

lemma wightmanPreInner_add_right_raw {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) (Ψ Φ₁ Φ₂ : WightmanConfig ι →₀ ℂ) :
    wightmanPreInner S W Ψ (Φ₁ + Φ₂) =
      wightmanPreInner S W Ψ Φ₁ + wightmanPreInner S W Ψ Φ₂ := by
  unfold wightmanPreInner
  rw [← Finsupp.sum_add]
  refine Finsupp.sum_congr (fun A _ => ?_)
  rw [Finsupp.sum_add_index']
  · intro B
    simp
  · intro B c₁ c₂
    ring

lemma wightmanPreInner_smul_left_raw {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) (c : ℂ) (Ψ Φ : WightmanConfig ι →₀ ℂ) :
    wightmanPreInner S W (c • Ψ) Φ =
      star c * wightmanPreInner S W Ψ Φ := by
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

lemma wightmanPreInner_smul_right_raw {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) (c : ℂ) (Ψ Φ : WightmanConfig ι →₀ ℂ) :
    wightmanPreInner S W Ψ (c • Φ) =
      c * wightmanPreInner S W Ψ Φ := by
  unfold wightmanPreInner
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr (fun A _ => ?_)
  rw [Finsupp.sum_smul_index, Finsupp.mul_sum]
  · refine Finsupp.sum_congr (fun B _ => ?_)
    ring
  · intro B
    simp

@[simp]
lemma wightmanPreInner_single_single {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) (A B : WightmanConfig ι) :
    wightmanPreInner S W (Finsupp.single A 1) (Finsupp.single B 1) =
      wightmanKernel S W A B := by
  unfold wightmanPreInner
  simp

lemma wightmanPreInner_sum_left {α : Type*}
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    (s : Finset α) (Ψ : α → WightmanConfig ι →₀ ℂ) (Φ : WightmanConfig ι →₀ ℂ) :
    wightmanPreInner S W (∑ a ∈ s, Ψ a) Φ =
      ∑ a ∈ s, wightmanPreInner S W (Ψ a) Φ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, wightmanPreInner_zero_left]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, wightmanPreInner_add_left_raw, ih]

lemma wightmanPreInner_sum_right {α : Type*}
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    (Ψ : WightmanConfig ι →₀ ℂ) (s : Finset α) (Φ : α → WightmanConfig ι →₀ ℂ) :
    wightmanPreInner S W Ψ (∑ a ∈ s, Φ a) =
      ∑ a ∈ s, wightmanPreInner S W Ψ (Φ a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, wightmanPreInner_zero_right]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, wightmanPreInner_add_right_raw, ih]

lemma wightmanPreInner_single_add_smul_single
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    (A B : WightmanConfig ι) (c : ℂ) :
    wightmanPreInner S W
      (Finsupp.single A 1 + c • Finsupp.single B 1)
      (Finsupp.single A 1 + c • Finsupp.single B 1) =
      wightmanKernel S W A A +
        c * wightmanKernel S W A B +
        star c * wightmanKernel S W B A +
        (star c * c) * wightmanKernel S W B B := by
  rw [wightmanPreInner_add_left_raw, wightmanPreInner_add_right_raw,
      wightmanPreInner_add_right_raw, wightmanPreInner_smul_left_raw,
      wightmanPreInner_smul_left_raw, wightmanPreInner_smul_right_raw,
      wightmanPreInner_smul_right_raw, wightmanPreInner_single_single,
      wightmanPreInner_single_single, wightmanPreInner_single_single,
      wightmanPreInner_single_single]
  ring

theorem wightmanKernelHermiticity_of_compactPositivity
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {W : WightmanFamily ι}
    (hpos : CompactPositivity S W) :
    WightmanKernelHermiticity S W := by
  intro A B
  have hAA : star (wightmanKernel S W A A) = wightmanKernel S W A A := by
    simpa using star_wightmanPreInner_self_of_compactPositivity hpos (Finsupp.single A 1)
  have hBB : star (wightmanKernel S W B B) = wightmanKernel S W B B := by
    simpa using star_wightmanPreInner_self_of_compactPositivity hpos (Finsupp.single B 1)
  have h_one := star_wightmanPreInner_self_of_compactPositivity hpos
    (Finsupp.single A 1 + (1 : ℂ) • Finsupp.single B 1)
  rw [wightmanPreInner_single_add_smul_single] at h_one
  simp only [star_one, one_mul, star_add, hAA, hBB] at h_one
  have h1 : star (wightmanKernel S W A B) + star (wightmanKernel S W B A) =
      wightmanKernel S W A B + wightmanKernel S W B A := by
    linear_combination h_one
  have h_I := star_wightmanPreInner_self_of_compactPositivity hpos
    (Finsupp.single A 1 + Complex.I • Finsupp.single B 1)
  rw [wightmanPreInner_single_add_smul_single] at h_I
  have h_star_I : star Complex.I = -Complex.I := by
    rw [Complex.star_def, Complex.conj_I]
  have h_I_norm : star Complex.I * Complex.I = 1 := by
    rw [h_star_I, neg_mul, Complex.I_mul_I, neg_neg]
  rw [h_I_norm, one_mul, h_star_I] at h_I
  simp only [star_add, star_mul', star_neg, h_star_I, neg_neg, hAA, hBB] at h_I
  have h2_I : Complex.I * (-Complex.I * star (wightmanKernel S W A B) +
      Complex.I * star (wightmanKernel S W B A)) =
      Complex.I * (Complex.I * wightmanKernel S W A B +
        -Complex.I * wightmanKernel S W B A) := by
    linear_combination Complex.I * h_I
  have h2 : star (wightmanKernel S W A B) - star (wightmanKernel S W B A) =
      -wightmanKernel S W A B + wightmanKernel S W B A := by
    calc star (wightmanKernel S W A B) - star (wightmanKernel S W B A)
      _ = -(Complex.I * Complex.I) * star (wightmanKernel S W A B) +
            (Complex.I * Complex.I) * star (wightmanKernel S W B A) := by
            rw [Complex.I_mul_I]
            ring
      _ = Complex.I * (-Complex.I * star (wightmanKernel S W A B) +
            Complex.I * star (wightmanKernel S W B A)) := by ring
      _ = Complex.I * (Complex.I * wightmanKernel S W A B +
            -Complex.I * wightmanKernel S W B A) := h2_I
      _ = (Complex.I * Complex.I) * wightmanKernel S W A B -
            (Complex.I * Complex.I) * wightmanKernel S W B A := by ring
      _ = -wightmanKernel S W A B + wightmanKernel S W B A := by
            rw [Complex.I_mul_I]
            ring
  linear_combination (1 / 2 : ℂ) * h1 - (1 / 2 : ℂ) * h2

theorem wightmanKernelHermiticity_of_positivity
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {W : WightmanFamily ι}
    (hpos : Positivity S W) :
    WightmanKernelHermiticity S W :=
  wightmanKernelHermiticity_of_compactPositivity (compactPositivity_of_positivity hpos)

def wightmanPositiveDataOfCompactPositivity
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    (hpos : CompactPositivity S W) :
    WightmanPositiveData R S where
  W := W
  hermiticity := wightmanKernelHermiticity_of_compactPositivity hpos
  positivity := wightmanKernelPositive_of_compactPositivity hpos

def wightmanPositiveDataOfPositivity
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    (hpos : Positivity S W) :
    WightmanPositiveData R S where
  W := W
  hermiticity := wightmanKernelHermiticity_of_positivity hpos
  positivity := wightmanKernelPositive_of_positivity hpos

@[simp]
lemma wightmanPositiveDataOfPositivity_W
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    (hpos : Positivity S W) :
    (wightmanPositiveDataOfPositivity S W hpos).W = W := rfl

@[ext]
lemma wightmanPositiveData_ext {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {WData₁ WData₂ : WightmanPositiveData R S} (hW : WData₁.W = WData₂.W) :
    WData₁ = WData₂ := by
  cases WData₁
  cases WData₂
  congr

lemma wightmanPositiveDataOfPositivity_eq_wightmanPositiveDataOfOSData
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hpos : Positivity S W) (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x) :
    wightmanPositiveDataOfPositivity S W hpos =
      wightmanPositiveDataOfOSData D W hspec h_schw :=
  rfl

def wightmanCompactBorchersFinsupp (N : ℕ)
    (F : ∀ j : ℕ, (Fin j → ι) → CompactSchwartz j) :
    WightmanConfig ι →₀ ℂ :=
  ∑ j ∈ Finset.range (N + 1), ∑ α : Fin j → ι,
    Finsupp.single ⟨j, (α, F j α)⟩ 1

theorem wightmanPreInner_wightmanCompactBorchersFinsupp
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    (N : ℕ) (F F' : ∀ j : ℕ, (Fin j → ι) → CompactSchwartz j) :
    wightmanPreInner S W
      (wightmanCompactBorchersFinsupp N F)
      (wightmanCompactBorchersFinsupp N F') =
      ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
        ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
          (∏ i : Fin j, S.C (α i) (β i)) *
            W (j + k) (Fin.append (β ∘ Fin.rev) α')
              (wightmanConcatSchwartz j k (F j α) (F' k α')) := by
  unfold wightmanCompactBorchersFinsupp
  rw [wightmanPreInner_sum_left]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [wightmanPreInner_sum_left]
  have h_comm :
      (∑ α : Fin j → ι,
        wightmanPreInner S W (Finsupp.single ⟨j, (α, F j α)⟩ 1)
          (∑ k ∈ Finset.range (N + 1), ∑ α' : Fin k → ι,
            Finsupp.single ⟨k, (α', F' k α')⟩ 1)) =
      ∑ k ∈ Finset.range (N + 1), ∑ α : Fin j → ι, ∑ α' : Fin k → ι,
        wightmanKernel S W ⟨j, (α, F j α)⟩ ⟨k, (α', F' k α')⟩ := by
    have h_inner : ∀ α : Fin j → ι,
        wightmanPreInner S W (Finsupp.single ⟨j, (α, F j α)⟩ 1)
          (∑ k ∈ Finset.range (N + 1), ∑ α' : Fin k → ι,
            Finsupp.single ⟨k, (α', F' k α')⟩ 1) =
        ∑ k ∈ Finset.range (N + 1), ∑ α' : Fin k → ι,
          wightmanKernel S W ⟨j, (α, F j α)⟩ ⟨k, (α', F' k α')⟩ := by
      intro α
      rw [wightmanPreInner_sum_right]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [wightmanPreInner_sum_right]
      refine Finset.sum_congr rfl (fun α' _ => ?_)
      exact wightmanPreInner_single_single S W _ _
    simp_rw [h_inner]
    exact Finset.sum_comm
  rw [h_comm]
  rfl

theorem wightmanPreInner_self_nonneg_of_wightmanPositiveData
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Ψ : WightmanConfig ι →₀ ℂ) :
    0 ≤ wightmanPreInner S WData.W Ψ Ψ := by
  rw [Complex.nonneg_iff]
  refine ⟨WData.positivity Ψ, ?_⟩
  have h_conj := wightmanPreInner_conj_symm WData Ψ Ψ
  rw [Complex.star_def, Complex.conj_eq_iff_im] at h_conj
  exact h_conj.symm

theorem compactPositivity_of_wightmanPositiveData
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) :
    CompactPositivity S WData.W := by
  intro N F
  rw [← wightmanPreInner_wightmanCompactBorchersFinsupp S WData.W N F F]
  exact wightmanPreInner_self_nonneg_of_wightmanPositiveData WData
    (wightmanCompactBorchersFinsupp N F)

theorem compactPositivity_iff_wightmanKernelPositive_and_hermiticity
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι) :
    CompactPositivity S W ↔
      (WightmanKernelPositive S W ∧ WightmanKernelHermiticity S W) :=
  ⟨fun hpos =>
    ⟨wightmanKernelPositive_of_compactPositivity hpos,
     wightmanKernelHermiticity_of_compactPositivity hpos⟩,
   fun ⟨hpos, hherm⟩ =>
    compactPositivity_of_wightmanPositiveData
      { W := W, hermiticity := hherm, positivity := hpos }⟩

theorem positivity_of_compactPositivity_of_zeroMomentumSpectrumCondition
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {W : WightmanFamily ι}
    (hspec : ZeroMomentumSpectrumCondition W) (hcpos : CompactPositivity S W) :
    Positivity S W := by
  intro N F G hG
  let Fc : ∀ j : ℕ, (Fin j → ι) → CompactSchwartz j := fun j α =>
    compactSchwartzSMul j (∫ y : Fin j → Fin 4 → ℝ, F j α y)
      (momentumWavepacketCompactSchwartz j 0)
  have h_int : ∀ (j : ℕ) (α : Fin j → ι),
      (∫ y : Fin j → Fin 4 → ℝ, (Fc j α).val y) =
        ∫ y : Fin j → Fin 4 → ℝ, F j α y := by
    intro j α
    change (∫ y : Fin j → Fin 4 → ℝ,
        (∫ z : Fin j → Fin 4 → ℝ, F j α z) * momentumWavepacketSchwartz j 0 y) =
      ∫ y : Fin j → Fin 4 → ℝ, F j α y
    rw [MeasureTheory.integral_const_mul, integral_momentumWavepacketSchwartz_zero, mul_one]
  have h_eq1 := wightmanSesquilinear_eq_vladimirovSesquilinear S W hspec N F F G hG
  have h_eq2 := wightmanSesquilinear_eq_vladimirovSesquilinear S W hspec N
    (fun j α => (Fc j α).val) (fun k α' => (Fc k α').val)
    (fun j k α α' => wightmanConcatSchwartz j k (Fc j α) (Fc k α'))
    (fun _ _ _ _ _ => rfl)
  simp_rw [h_int] at h_eq2
  rw [h_eq1, ← h_eq2]
  exact hcpos N Fc

theorem positivity_iff_compactPositivity_of_zeroMomentumSpectrumCondition
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) {W : WightmanFamily ι}
    (hspec : ZeroMomentumSpectrumCondition W) :
    Positivity S W ↔ CompactPositivity S W :=
  ⟨compactPositivity_of_positivity,
   positivity_of_compactPositivity_of_zeroMomentumSpectrumCondition hspec⟩

theorem positivity_iff_wightmanKernelPositive_and_hermiticity_of_zeroMomentumSpectrumCondition
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) {W : WightmanFamily ι}
    (hspec : ZeroMomentumSpectrumCondition W) :
    Positivity S W ↔
      (WightmanKernelPositive S W ∧ WightmanKernelHermiticity S W) :=
  (positivity_iff_compactPositivity_of_zeroMomentumSpectrumCondition S hspec).trans
    (compactPositivity_iff_wightmanKernelPositive_and_hermiticity S W)

namespace OSEuclideanTubeBridge

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

def toWightmanPositiveData (B : OSEuclideanTubeBridge R S η 𝒮) :
    WightmanPositiveData R S :=
  wightmanPositiveDataOfPositivity S B.W B.positivity

@[simp]
lemma toWightmanPositiveData_W (B : OSEuclideanTubeBridge R S η 𝒮) :
    B.toWightmanPositiveData.W = B.W := rfl

abbrev WightmanHilbertSpace (B : OSEuclideanTubeBridge R S η 𝒮) : Type _ :=
  WightmanHilbert B.toWightmanPositiveData

def wightmanVacuumVec (B : OSEuclideanTubeBridge R S η 𝒮) : B.WightmanHilbertSpace :=
  wightmanVacuum B.toWightmanPositiveData

def wightmanBasisVec (B : OSEuclideanTubeBridge R S η 𝒮) (A : WightmanConfig ι) :
    B.WightmanHilbertSpace :=
  wightmanBasis B.toWightmanPositiveData A

end OSEuclideanTubeBridge

namespace ForwardConeOSEuclideanTubeBridge

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

def toWightmanPositiveData (B : ForwardConeOSEuclideanTubeBridge R S η 𝒮) :
    WightmanPositiveData R S :=
  wightmanPositiveDataOfPositivity S B.W B.positivity

@[simp]
lemma toWightmanPositiveData_W (B : ForwardConeOSEuclideanTubeBridge R S η 𝒮) :
    B.toWightmanPositiveData.W = B.W := rfl

abbrev WightmanHilbertSpace (B : ForwardConeOSEuclideanTubeBridge R S η 𝒮) : Type _ :=
  WightmanHilbert B.toWightmanPositiveData

def wightmanVacuumVec (B : ForwardConeOSEuclideanTubeBridge R S η 𝒮) :
    B.WightmanHilbertSpace :=
  wightmanVacuum B.toWightmanPositiveData

def wightmanBasisVec (B : ForwardConeOSEuclideanTubeBridge R S η 𝒮) (A : WightmanConfig ι) :
    B.WightmanHilbertSpace :=
  wightmanBasis B.toWightmanPositiveData A

end ForwardConeOSEuclideanTubeBridge

namespace OSReconstructedWightman

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

def toWightmanPositiveData (P : OSReconstructedWightman R S η 𝒮) :
    WightmanPositiveData R S :=
  wightmanPositiveDataOfPositivity S P.W P.positivity

@[simp]
lemma toWightmanPositiveData_W (P : OSReconstructedWightman R S η 𝒮) :
    P.toWightmanPositiveData.W = P.W := rfl

abbrev WightmanHilbertSpace (P : OSReconstructedWightman R S η 𝒮) : Type _ :=
  WightmanHilbert P.toWightmanPositiveData

def wightmanVacuumVec (P : OSReconstructedWightman R S η 𝒮) : P.WightmanHilbertSpace :=
  wightmanVacuum P.toWightmanPositiveData

def wightmanBasisVec (P : OSReconstructedWightman R S η 𝒮) (A : WightmanConfig ι) :
    P.WightmanHilbertSpace :=
  wightmanBasis P.toWightmanPositiveData A

def osWightmanLinearIsometryEquiv (P : OSReconstructedWightman R S η 𝒮)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = vladimirovSchwinger P.W n α x) :
    P.Hilbert ≃ₗᵢ[ℂ] P.WightmanHilbertSpace :=
  vladimirovOSWightmanLinearIsometryEquiv P.osData P.W P.spectrum h_schw

@[simp]
theorem osWightmanLinearIsometryEquiv_vacuum (P : OSReconstructedWightman R S η 𝒮)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = vladimirovSchwinger P.W n α x) :
    P.osWightmanLinearIsometryEquiv h_schw P.vacuum = P.wightmanVacuumVec :=
  vladimirovOSWightmanLinearIsometryEquiv_osVacuum P.osData P.W P.spectrum h_schw

@[simp]
theorem osWightmanLinearIsometryEquiv_symm_wightmanVacuum
    (P : OSReconstructedWightman R S η 𝒮)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = vladimirovSchwinger P.W n α x) :
    (P.osWightmanLinearIsometryEquiv h_schw).symm P.wightmanVacuumVec = P.vacuum :=
  vladimirovOSWightmanLinearIsometryEquiv_symm_wightmanVacuum P.osData P.W P.spectrum h_schw

end OSReconstructedWightman

namespace ForwardConeOSReconstructedWightman

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

def toWightmanPositiveData (P : ForwardConeOSReconstructedWightman R S η 𝒮) :
    WightmanPositiveData R S :=
  wightmanPositiveDataOfPositivity S P.W P.positivity

@[simp]
lemma toWightmanPositiveData_W (P : ForwardConeOSReconstructedWightman R S η 𝒮) :
    P.toWightmanPositiveData.W = P.W := rfl

abbrev WightmanHilbertSpace (P : ForwardConeOSReconstructedWightman R S η 𝒮) : Type _ :=
  WightmanHilbert P.toWightmanPositiveData

def wightmanVacuumVec (P : ForwardConeOSReconstructedWightman R S η 𝒮) :
    P.WightmanHilbertSpace :=
  wightmanVacuum P.toWightmanPositiveData

def wightmanBasisVec (P : ForwardConeOSReconstructedWightman R S η 𝒮) (A : WightmanConfig ι) :
    P.WightmanHilbertSpace :=
  wightmanBasis P.toWightmanPositiveData A

end ForwardConeOSReconstructedWightman

namespace ForwardConeSpectralFamily

def toWightmanPositiveData (F : ForwardConeSpectralFamily ι)
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (hpos : Positivity S F.toWightmanFamily) :
    WightmanPositiveData R S :=
  wightmanPositiveDataOfPositivity S F.toWightmanFamily hpos

@[simp]
lemma toWightmanPositiveData_W (F : ForwardConeSpectralFamily ι)
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (hpos : Positivity S F.toWightmanFamily) :
    (F.toWightmanPositiveData S hpos).W = F.toWightmanFamily := rfl

end ForwardConeSpectralFamily

theorem phase1_wightman_positivity_bridge_master
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι) :
    (CompactPositivity S W ↔
      (WightmanKernelPositive S W ∧ WightmanKernelHermiticity S W)) ∧
    (Positivity S W → CompactPositivity S W) ∧
    (Positivity S W → WightmanKernelPositive S W) ∧
    (Positivity S W → WightmanKernelHermiticity S W) ∧
    (ZeroMomentumSpectrumCondition W →
      (Positivity S W ↔
        (WightmanKernelPositive S W ∧ WightmanKernelHermiticity S W))) :=
  ⟨compactPositivity_iff_wightmanKernelPositive_and_hermiticity S W,
   compactPositivity_of_positivity,
   wightmanKernelPositive_of_positivity,
   wightmanKernelHermiticity_of_positivity,
   positivity_iff_wightmanKernelPositive_and_hermiticity_of_zeroMomentumSpectrumCondition S⟩

omit [Fintype ι] [DecidableEq ι] in
noncomputable def schwartzDiagTranslateN (n : ℕ) (a : Fin 4 → ℝ) :
    SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (hasTemperateGrowth_sub_const_n n (fun _ => a))
    (antilipschitzWith_sub_const_n n (fun _ => a))

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma schwartzDiagTranslateN_apply (n : ℕ) (a : Fin 4 → ℝ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (x : Fin n → Fin 4 → ℝ) :
    schwartzDiagTranslateN n a f x = f (fun i => x i - a) := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma schwartzDiagTranslateN_shift (n : ℕ) (a : Fin 4 → ℝ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (x : Fin n → Fin 4 → ℝ) :
    schwartzDiagTranslateN n a f (fun i => x i + a) = f x := by
  rw [schwartzDiagTranslateN_apply]
  have h_sub : (fun i : Fin n => x i + a - a) = x := by
    ext i μ
    simp
  rw [h_sub]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma schwartzDiagTranslateN_zero (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    schwartzDiagTranslateN n 0 f = f := by
  ext x
  simp

omit [Fintype ι] [DecidableEq ι] in
lemma schwartzDiagTranslateN_add (n : ℕ) (a b : Fin 4 → ℝ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    schwartzDiagTranslateN n (a + b) f =
      schwartzDiagTranslateN n a (schwartzDiagTranslateN n b f) := by
  ext x
  simp only [schwartzDiagTranslateN_apply]
  congr 1
  ext i μ
  simp only [Pi.sub_apply, Pi.add_apply]
  ring

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma schwartzDiagTranslateN_fin0 (a : Fin 4 → ℝ)
    (f : SchwartzMap (Fin 0 → Fin 4 → ℝ) ℂ) :
    schwartzDiagTranslateN 0 a f = f := by
  ext x
  rw [schwartzDiagTranslateN_apply]
  congr 1
  ext i
  exact Fin.elim0 i

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma integral_schwartzDiagTranslateN (n : ℕ) (a : Fin 4 → ℝ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    (∫ x : Fin n → Fin 4 → ℝ, schwartzDiagTranslateN n a f x) =
      ∫ x : Fin n → Fin 4 → ℝ, f x :=
  MeasureTheory.integral_sub_right_eq_self (fun x => f x) (fun _ : Fin n => a)

omit [Fintype ι] [DecidableEq ι] in
lemma hasCompactSupport_schwartzDiagTranslateN (n : ℕ) (a : Fin 4 → ℝ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hf : HasCompactSupport (f : (Fin n → Fin 4 → ℝ) → ℂ)) :
    HasCompactSupport (schwartzDiagTranslateN n a f : (Fin n → Fin 4 → ℝ) → ℂ) := by
  let v0 : Fin n → Fin 4 → ℝ := fun _ => a
  have hK : IsCompact
      ((fun y : Fin n → Fin 4 → ℝ => y + v0) ''
        tsupport (f : (Fin n → Fin 4 → ℝ) → ℂ)) :=
    hf.isCompact.image (continuous_id.add continuous_const)
  refine HasCompactSupport.of_support_subset_isCompact hK ?_
  intro x hx
  rw [Function.mem_support] at hx
  refine ⟨x - v0, subset_tsupport _ (Function.mem_support.mpr hx), ?_⟩
  ext i μ
  simp [v0]

omit [Fintype ι] [DecidableEq ι] in
noncomputable def compactSchwartzTranslate (n : ℕ) (a : Fin 4 → ℝ)
    (f : CompactSchwartz n) : CompactSchwartz n :=
  ⟨schwartzDiagTranslateN n a f.val,
   hasCompactSupport_schwartzDiagTranslateN n a f.val f.property⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma compactSchwartzTranslate_val (n : ℕ) (a : Fin 4 → ℝ) (f : CompactSchwartz n) :
    (compactSchwartzTranslate n a f).val = schwartzDiagTranslateN n a f.val := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma compactSchwartzTranslate_zero (n : ℕ) (f : CompactSchwartz n) :
    compactSchwartzTranslate n 0 f = f := by
  ext x
  simp

omit [Fintype ι] [DecidableEq ι] in
lemma compactSchwartzTranslate_add (n : ℕ) (a b : Fin 4 → ℝ)
    (f : CompactSchwartz n) :
    compactSchwartzTranslate n (a + b) f =
      compactSchwartzTranslate n a (compactSchwartzTranslate n b f) := by
  apply Subtype.ext
  exact schwartzDiagTranslateN_add n a b f.val

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma compactSchwartzTranslate_fin0 (a : Fin 4 → ℝ) (f : CompactSchwartz 0) :
    compactSchwartzTranslate 0 a f = f := by
  apply Subtype.ext
  exact schwartzDiagTranslateN_fin0 a f.val

omit [Fintype ι] [DecidableEq ι] in
lemma wightmanConcatSchwartz_translate_shift (j k : ℕ) (a : Fin 4 → ℝ)
    (f : CompactSchwartz j) (g : CompactSchwartz k)
    (x : Fin (j + k) → Fin 4 → ℝ) :
    wightmanConcatSchwartz j k
      (compactSchwartzTranslate j a f) (compactSchwartzTranslate k a g)
      (fun i => x i + a) =
    wightmanConcatSchwartz j k f g x := by
  simp only [wightmanConcatSchwartz_apply, compactSchwartzTranslate_val,
    schwartzDiagTranslateN_apply, add_sub_cancel_right]

omit [Fintype ι] [DecidableEq ι] in
lemma sum_minkowskiInner_left {n : ℕ} (p : Fin n → Fin 4 → ℝ) (a : Fin 4 → ℝ) :
    (∑ k : Fin n, minkowskiInner (p k) a) =
      minkowskiInner (∑ k : Fin n, p k) a := by
  simp only [minkowskiInner_explicit, Finset.sum_apply, Finset.sum_mul,
    Finset.sum_sub_distrib]

omit [Fintype ι] [DecidableEq ι] in
lemma minkowskiFourier_shift_n {n : ℕ}
    (h h' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (a : Fin 4 → ℝ)
    (h_shift : ∀ x, h' (fun i => x i + a) = h x)
    (p : Fin n → Fin 4 → ℝ) :
    minkowskiFourier h' p =
      Complex.exp
        (-(Complex.I * ((minkowskiInner (∑ k : Fin n, p k) a : ℝ) : ℂ))) *
        minkowskiFourier h p := by
  dsimp [minkowskiFourier]
  let v0 : Fin n → Fin 4 → ℝ := fun _ => a
  have h_int := MeasureTheory.integral_add_right_eq_self
    (μ := (MeasureTheory.MeasureSpace.volume :
      MeasureTheory.Measure (Fin n → Fin 4 → ℝ)))
    (fun y : Fin n → Fin 4 → ℝ =>
      h' y * Complex.exp
        (-(Complex.I * ((∑ k, minkowskiInner (p k) (y k) : ℝ) : ℂ)))) v0
  rw [← h_int, ← MeasureTheory.integral_const_mul]
  congr 1
  ext x
  have hx_add : x + v0 = fun i => x i + a := rfl
  have h_h' : h' (x + v0) = h x := by
    rw [hx_add]
    exact h_shift x
  dsimp
  rw [h_h']
  have h_sum : (∑ k : Fin n, minkowskiInner (p k) (x k + v0 k)) =
      (∑ k : Fin n, minkowskiInner (p k) (x k)) +
        minkowskiInner (∑ k : Fin n, p k) a := by
    have h_add := (minkowskiPhaseLM n p).map_add x v0
    change (∑ k : Fin n, minkowskiInner (p k) (x k + v0 k)) =
      (∑ k : Fin n, minkowskiInner (p k) (x k)) +
        (∑ k : Fin n, minkowskiInner (p k) a) at h_add
    rw [h_add, sum_minkowskiInner_left]
  have h_exp :
      -(Complex.I * (((∑ k : Fin n, minkowskiInner (p k) (x k)) +
        minkowskiInner (∑ k : Fin n, p k) a : ℝ) : ℂ)) =
      (-(Complex.I * ((minkowskiInner (∑ k : Fin n, p k) a : ℝ) : ℂ))) +
        (-(Complex.I * ((∑ k : Fin n, minkowskiInner (p k) (x k) : ℝ) : ℂ))) := by
    push_cast
    ring
  rw [h_sum, h_exp, Complex.exp_add]
  ring

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma minkowskiFourier_schwartzDiagTranslateN (n : ℕ) (a : Fin 4 → ℝ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (p : Fin n → Fin 4 → ℝ) :
    minkowskiFourier (schwartzDiagTranslateN n a f) p =
      Complex.exp
        (-(Complex.I * ((minkowskiInner (∑ k : Fin n, p k) a : ℝ) : ℂ))) *
        minkowskiFourier f p :=
  minkowskiFourier_shift_n f (schwartzDiagTranslateN n a f) a
    (schwartzDiagTranslateN_shift n a f) p

omit [Fintype ι] [DecidableEq ι] in
def WightmanTranslationInvariant (W : WightmanFamily ι) : Prop :=
  ∀ (n : ℕ) (α : Fin n → ι) (a : Fin 4 → ℝ)
    (f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
    (∀ x : Fin n → Fin 4 → ℝ, f' (fun i => x i + a) = f x) →
    W n α f' = W n α f

theorem wightmanTranslationInvariant_of_poincare
    (R : HolomorphicLorentzRep ι) {W : WightmanFamily ι}
    (hP : PoincareCovariant R W) :
    WightmanTranslationInvariant W :=
  fun n α a f f' hf' => translationInvariant_of_poincare R W hP n a α f f' hf'

omit [Fintype ι] [DecidableEq ι] in
theorem wightmanTranslationInvariant_of_tubeTranslationInvariant
    {W : WightmanFamily ι} (E : TubeExtension W)
    (htrans : TubeTranslationInvariant E) :
    WightmanTranslationInvariant W :=
  wightman_translationInvariant_of_tubeTranslationInvariant E htrans

omit [Fintype ι] [DecidableEq ι] in
noncomputable def wightmanConfigTranslate (a : Fin 4 → ℝ)
    (A : WightmanConfig ι) : WightmanConfig ι :=
  ⟨A.1, (A.2.1, compactSchwartzTranslate A.1 a A.2.2)⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanConfigTranslate_zero_apply (A : WightmanConfig ι) :
    wightmanConfigTranslate 0 A = A := by
  rcases A with ⟨n, α, f⟩
  dsimp [wightmanConfigTranslate]
  rw [compactSchwartzTranslate_zero]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanConfigTranslate_zero :
    wightmanConfigTranslate (ι := ι) 0 = id := by
  ext A : 1
  exact wightmanConfigTranslate_zero_apply A

omit [Fintype ι] [DecidableEq ι] in
lemma wightmanConfigTranslate_add_apply (a b : Fin 4 → ℝ)
    (A : WightmanConfig ι) :
    wightmanConfigTranslate (a + b) A =
      wightmanConfigTranslate a (wightmanConfigTranslate b A) := by
  rcases A with ⟨n, α, f⟩
  dsimp [wightmanConfigTranslate]
  rw [compactSchwartzTranslate_add]

omit [Fintype ι] [DecidableEq ι] in
lemma wightmanConfigTranslate_add (a b : Fin 4 → ℝ) :
    wightmanConfigTranslate (ι := ι) (a + b) =
      wightmanConfigTranslate a ∘ wightmanConfigTranslate b := by
  ext A : 1
  exact wightmanConfigTranslate_add_apply a b A

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanConfigTranslate_vacuum (a : Fin 4 → ℝ) :
    wightmanConfigTranslate a (wightmanVacuumConfig ι) =
      wightmanVacuumConfig ι := by
  dsimp [wightmanConfigTranslate, wightmanVacuumConfig, wightmanBaseConfig]
  rw [compactSchwartzTranslate_fin0]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma integral_wightmanConfigTranslate (a : Fin 4 → ℝ)
    (A : WightmanConfig ι) :
    (∫ y : Fin (wightmanConfigTranslate a A).1 → Fin 4 → ℝ,
      (wightmanConfigTranslate a A).2.2.val y) =
      ∫ y : Fin A.1 → Fin 4 → ℝ, A.2.2.val y :=
  integral_schwartzDiagTranslateN A.1 a A.2.2.val

theorem wightmanKernel_translate_invariant
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {W : WightmanFamily ι} (htrans : WightmanTranslationInvariant W)
    (a : Fin 4 → ℝ) (A B : WightmanConfig ι) :
    wightmanKernel S W
      (wightmanConfigTranslate a A) (wightmanConfigTranslate a B) =
    wightmanKernel S W A B := by
  rcases A with ⟨j, α, f⟩
  rcases B with ⟨k, α', g⟩
  dsimp [wightmanKernel, wightmanConfigTranslate]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  congr 1
  exact htrans (j + k) (osConcatIdx j k β α') a
    (wightmanConcatSchwartz j k f g)
    (wightmanConcatSchwartz j k
      (compactSchwartzTranslate j a f) (compactSchwartzTranslate k a g))
    (wightmanConcatSchwartz_translate_shift j k a f g)

theorem wightmanKernel_translate_symm
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {W : WightmanFamily ι} (htrans : WightmanTranslationInvariant W)
    (a : Fin 4 → ℝ) (A B : WightmanConfig ι) :
    wightmanKernel S W (wightmanConfigTranslate a A) B =
      wightmanKernel S W A (wightmanConfigTranslate (-a) B) := by
  have h := wightmanKernel_translate_invariant S htrans (-a)
    (wightmanConfigTranslate a A) B
  rw [← wightmanConfigTranslate_add_apply, neg_add_cancel,
      wightmanConfigTranslate_zero_apply] at h
  exact h.symm

noncomputable def wightmanLiftConfigMap
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (g : WightmanConfig ι → WightmanConfig ι) :
    WightmanPreHilbertSpace WData →ₗ[ℂ] WightmanPreHilbertSpace WData :=
  (WightmanPreHilbertSpace.equivFinsupp WData).symm.toLinearMap.comp
    ((Finsupp.lmapDomain ℂ ℂ g).comp
      (WightmanPreHilbertSpace.equivFinsupp WData).toLinearMap)

@[simp]
lemma toFinsupp_wightmanLiftConfigMap
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (g : WightmanConfig ι → WightmanConfig ι)
    (Ψ : WightmanPreHilbertSpace WData) :
    (wightmanLiftConfigMap WData g Ψ).toFinsupp =
      Finsupp.mapDomain g Ψ.toFinsupp := rfl

@[simp]
lemma wightmanLiftConfigMap_id
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) :
    wightmanLiftConfigMap WData id = LinearMap.id := by
  ext Ψ : 1
  apply WightmanPreHilbertSpace.ext
  simp

lemma wightmanLiftConfigMap_comp
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (g₁ g₂ : WightmanConfig ι → WightmanConfig ι) :
    wightmanLiftConfigMap WData (g₁ ∘ g₂) =
      (wightmanLiftConfigMap WData g₁).comp
        (wightmanLiftConfigMap WData g₂) := by
  ext Ψ : 1
  apply WightmanPreHilbertSpace.ext
  simp [Finsupp.mapDomain_comp]

@[simp]
lemma wightmanLiftConfigMap_wightmanBasisPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (g : WightmanConfig ι → WightmanConfig ι) (A : WightmanConfig ι) :
    wightmanLiftConfigMap WData g (wightmanBasisPre WData A) =
      wightmanBasisPre WData (g A) := by
  apply WightmanPreHilbertSpace.ext
  simp [wightmanBasisPre]

lemma inner_wightmanLiftConfigMap
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (g₁ g₂ : WightmanConfig ι → WightmanConfig ι)
    (Ψ Φ : WightmanPreHilbertSpace WData) :
    ⟪wightmanLiftConfigMap WData g₁ Ψ,
      wightmanLiftConfigMap WData g₂ Φ⟫_ℂ =
      Ψ.toFinsupp.sum fun A cA =>
        Φ.toFinsupp.sum fun B cB =>
          star cA * cB * wightmanKernel S WData.W (g₁ A) (g₂ B) := by
  rw [WightmanPreHilbertSpace.inner_def, toFinsupp_wightmanLiftConfigMap,
      toFinsupp_wightmanLiftConfigMap]
  unfold wightmanPreInner
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp)
    (fun _ _ _ => by simp [add_mul, Finsupp.sum_add])]
  refine Finsupp.sum_congr (fun A _ => ?_)
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp)
    (fun _ _ _ => by ring)]

noncomputable def wightmanTranslateLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (a : Fin 4 → ℝ) :
    WightmanPreHilbertSpace WData →ₗ[ℂ] WightmanPreHilbertSpace WData :=
  wightmanLiftConfigMap WData (wightmanConfigTranslate a)

@[simp]
lemma wightmanTranslateLM_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) :
    wightmanTranslateLM WData 0 = LinearMap.id := by
  unfold wightmanTranslateLM
  rw [wightmanConfigTranslate_zero, wightmanLiftConfigMap_id]

lemma wightmanTranslateLM_add
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (a b : Fin 4 → ℝ) :
    wightmanTranslateLM WData (a + b) =
      (wightmanTranslateLM WData a).comp (wightmanTranslateLM WData b) := by
  unfold wightmanTranslateLM
  rw [wightmanConfigTranslate_add, wightmanLiftConfigMap_comp]

@[simp]
lemma wightmanTranslateLM_wightmanBasisPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (a : Fin 4 → ℝ)
    (A : WightmanConfig ι) :
    wightmanTranslateLM WData a (wightmanBasisPre WData A) =
      wightmanBasisPre WData (wightmanConfigTranslate a A) :=
  wightmanLiftConfigMap_wightmanBasisPre WData (wightmanConfigTranslate a) A

@[simp]
lemma wightmanTranslateLM_vacuumPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (a : Fin 4 → ℝ) :
    wightmanTranslateLM WData a (wightmanVacuumPre WData) =
      wightmanVacuumPre WData := by
  unfold wightmanVacuumPre
  rw [wightmanTranslateLM_wightmanBasisPre, wightmanConfigTranslate_vacuum]

theorem inner_wightmanTranslateLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (a : Fin 4 → ℝ) (Ψ Φ : WightmanPreHilbertSpace WData) :
    ⟪wightmanTranslateLM WData a Ψ, wightmanTranslateLM WData a Φ⟫_ℂ =
      ⟪Ψ, Φ⟫_ℂ := by
  unfold wightmanTranslateLM
  rw [inner_wightmanLiftConfigMap WData
      (wightmanConfigTranslate a) (wightmanConfigTranslate a) Ψ Φ,
      WightmanPreHilbertSpace.inner_def]
  unfold wightmanPreInner
  refine Finsupp.sum_congr (fun A _ => Finsupp.sum_congr (fun B _ => ?_))
  rw [wightmanKernel_translate_invariant S htrans a A B]

theorem norm_wightmanTranslateLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (a : Fin 4 → ℝ) (Ψ : WightmanPreHilbertSpace WData) :
    ‖wightmanTranslateLM WData a Ψ‖ = ‖Ψ‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_wightmanTranslateLM WData htrans a Ψ Ψ]

noncomputable def wightmanTranslatePreCLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 4 → ℝ) :
    WightmanPreHilbertSpace WData →L[ℂ] WightmanPreHilbertSpace WData :=
  (wightmanTranslateLM WData a).mkContinuous 1 (fun Ψ => by
    rw [one_mul, norm_wightmanTranslateLM WData htrans a Ψ])

noncomputable def wightmanTranslate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 4 → ℝ) :
    WightmanHilbert WData →L[ℂ] WightmanHilbert WData :=
  (wightmanTranslatePreCLM WData htrans a).completion

@[simp]
lemma wightmanTranslate_toWightmanHilbert
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 4 → ℝ)
    (Ψ : WightmanPreHilbertSpace WData) :
    wightmanTranslate WData htrans a (toWightmanHilbert WData Ψ) =
      toWightmanHilbert WData (wightmanTranslateLM WData a Ψ) :=
  ContinuousLinearMap.completion_apply_coe
    (wightmanTranslatePreCLM WData htrans a) Ψ

@[simp]
theorem wightmanTranslate_wightmanBasis
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 4 → ℝ)
    (A : WightmanConfig ι) :
    wightmanTranslate WData htrans a (wightmanBasis WData A) =
      wightmanBasis WData (wightmanConfigTranslate a A) := by
  dsimp [wightmanBasis]
  rw [wightmanTranslate_toWightmanHilbert,
      wightmanTranslateLM_wightmanBasisPre]

@[simp]
theorem wightmanTranslate_vacuum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 4 → ℝ) :
    wightmanTranslate WData htrans a (wightmanVacuum WData) =
      wightmanVacuum WData := by
  dsimp [wightmanVacuum]
  rw [wightmanTranslate_toWightmanHilbert, wightmanTranslateLM_vacuumPre]

@[simp]
theorem wightmanTranslate_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) :
    wightmanTranslate WData htrans 0 =
      ContinuousLinearMap.id ℂ (WightmanHilbert WData) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change wightmanTranslate WData htrans 0 (toWightmanHilbert WData Ψ) =
      toWightmanHilbert WData Ψ
    rw [wightmanTranslate_toWightmanHilbert, wightmanTranslateLM_zero,
        LinearMap.id_apply]

theorem wightmanTranslate_add
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a b : Fin 4 → ℝ) :
    wightmanTranslate WData htrans (a + b) =
      (wightmanTranslate WData htrans a).comp
        (wightmanTranslate WData htrans b) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change wightmanTranslate WData htrans (a + b)
        (toWightmanHilbert WData Ψ) =
      wightmanTranslate WData htrans a
        (wightmanTranslate WData htrans b (toWightmanHilbert WData Ψ))
    rw [wightmanTranslate_toWightmanHilbert,
        wightmanTranslate_toWightmanHilbert,
        wightmanTranslate_toWightmanHilbert,
        wightmanTranslateLM_add, LinearMap.comp_apply]

theorem wightmanTranslate_neg_comp
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 4 → ℝ) :
    (wightmanTranslate WData htrans (-a)).comp
      (wightmanTranslate WData htrans a) =
    ContinuousLinearMap.id ℂ (WightmanHilbert WData) := by
  rw [← wightmanTranslate_add, neg_add_cancel, wightmanTranslate_zero]

theorem wightmanTranslate_comp_neg
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 4 → ℝ) :
    (wightmanTranslate WData htrans a).comp
      (wightmanTranslate WData htrans (-a)) =
    ContinuousLinearMap.id ℂ (WightmanHilbert WData) := by
  rw [← wightmanTranslate_add, add_neg_cancel, wightmanTranslate_zero]

theorem inner_wightmanTranslate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 4 → ℝ)
    (x y : WightmanHilbert WData) :
    ⟪wightmanTranslate WData htrans a x,
      wightmanTranslate WData htrans a y⟫_ℂ = ⟪x, y⟫_ℂ := by
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ Φ =>
    change ⟪wightmanTranslate WData htrans a (toWightmanHilbert WData Ψ),
        wightmanTranslate WData htrans a (toWightmanHilbert WData Φ)⟫_ℂ =
      ⟪toWightmanHilbert WData Ψ, toWightmanHilbert WData Φ⟫_ℂ
    rw [wightmanTranslate_toWightmanHilbert,
        wightmanTranslate_toWightmanHilbert,
        inner_toWightmanHilbert, inner_toWightmanHilbert,
        inner_wightmanTranslateLM WData htrans a Ψ Φ]

@[simp]
theorem norm_wightmanTranslate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 4 → ℝ)
    (x : WightmanHilbert WData) :
    ‖wightmanTranslate WData htrans a x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_wightmanTranslate WData htrans a x x]

theorem inner_wightmanTranslate_adjoint
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 4 → ℝ)
    (x y : WightmanHilbert WData) :
    ⟪wightmanTranslate WData htrans a x, y⟫_ℂ =
      ⟪x, wightmanTranslate WData htrans (-a) y⟫_ℂ := by
  rw [← inner_wightmanTranslate WData htrans (-a)
      (wightmanTranslate WData htrans a x) y]
  change ⟪((wightmanTranslate WData htrans (-a)).comp
      (wightmanTranslate WData htrans a)) x,
    wightmanTranslate WData htrans (-a) y⟫_ℂ = _
  rw [wightmanTranslate_neg_comp, ContinuousLinearMap.id_apply]

noncomputable def wightmanTranslateLinearIsometryEquiv
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 4 → ℝ) :
    WightmanHilbert WData ≃ₗᵢ[ℂ] WightmanHilbert WData where
  toFun := wightmanTranslate WData htrans a
  map_add' := (wightmanTranslate WData htrans a).map_add
  map_smul' := (wightmanTranslate WData htrans a).map_smul
  invFun := wightmanTranslate WData htrans (-a)
  left_inv x := by
    change ((wightmanTranslate WData htrans (-a)).comp
      (wightmanTranslate WData htrans a)) x = x
    rw [wightmanTranslate_neg_comp, ContinuousLinearMap.id_apply]
  right_inv x := by
    change ((wightmanTranslate WData htrans a).comp
      (wightmanTranslate WData htrans (-a))) x = x
    rw [wightmanTranslate_comp_neg, ContinuousLinearMap.id_apply]
  norm_map' := norm_wightmanTranslate WData htrans a

noncomputable def wightmanSpatialTranslate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 3 → ℝ) :
    WightmanHilbert WData →L[ℂ] WightmanHilbert WData :=
  wightmanTranslate WData htrans (euclidSpatialVec a)

noncomputable def wightmanTimeTranslate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (t : ℝ) :
    WightmanHilbert WData →L[ℂ] WightmanHilbert WData :=
  wightmanTranslate WData htrans (euclidTimeVec t)

@[simp]
theorem wightmanSpatialTranslate_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) :
    wightmanSpatialTranslate WData htrans 0 =
      ContinuousLinearMap.id ℂ (WightmanHilbert WData) := by
  unfold wightmanSpatialTranslate
  rw [euclidSpatialVec_zero, wightmanTranslate_zero]

theorem wightmanSpatialTranslate_add
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a b : Fin 3 → ℝ) :
    wightmanSpatialTranslate WData htrans (a + b) =
      (wightmanSpatialTranslate WData htrans a).comp
        (wightmanSpatialTranslate WData htrans b) := by
  unfold wightmanSpatialTranslate
  rw [euclidSpatialVec_add, wightmanTranslate_add]

@[simp]
theorem wightmanSpatialTranslate_vacuum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 3 → ℝ) :
    wightmanSpatialTranslate WData htrans a (wightmanVacuum WData) =
      wightmanVacuum WData :=
  wightmanTranslate_vacuum WData htrans (euclidSpatialVec a)

@[simp]
theorem wightmanTimeTranslate_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) :
    wightmanTimeTranslate WData htrans 0 =
      ContinuousLinearMap.id ℂ (WightmanHilbert WData) := by
  unfold wightmanTimeTranslate
  rw [euclidTimeVec_zero, wightmanTranslate_zero]

theorem wightmanTimeTranslate_add
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (t₁ t₂ : ℝ) :
    wightmanTimeTranslate WData htrans (t₁ + t₂) =
      (wightmanTimeTranslate WData htrans t₁).comp
        (wightmanTimeTranslate WData htrans t₂) := by
  unfold wightmanTimeTranslate
  rw [euclidTimeVec_add, wightmanTranslate_add]

@[simp]
theorem wightmanTimeTranslate_vacuum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (t : ℝ) :
    wightmanTimeTranslate WData htrans t (wightmanVacuum WData) =
      wightmanVacuum WData :=
  wightmanTranslate_vacuum WData htrans (euclidTimeVec t)

omit [Fintype ι] [DecidableEq ι] in
lemma euclidTimeVec_add_euclidSpatialVec (a : Fin 4 → ℝ) :
    euclidTimeVec (a 0) + euclidSpatialVec (spatialPart a) = a := by
  ext μ
  refine Fin.cases ?_ ?_ μ
  · simp [euclidTimeVec, euclidSpatialVec]
  · intro i
    simp [euclidTimeVec, euclidSpatialVec, spatialPart]

theorem wightmanTranslate_eq_time_comp_spatial
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 4 → ℝ) :
    wightmanTranslate WData htrans a =
      (wightmanTimeTranslate WData htrans (a 0)).comp
        (wightmanSpatialTranslate WData htrans (spatialPart a)) := by
  unfold wightmanTimeTranslate wightmanSpatialTranslate
  rw [← wightmanTranslate_add, euclidTimeVec_add_euclidSpatialVec]

theorem wightmanSpatialTranslate_comm_wightmanTimeTranslate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (a : Fin 3 → ℝ) (t : ℝ) :
    (wightmanSpatialTranslate WData htrans a).comp
      (wightmanTimeTranslate WData htrans t) =
    (wightmanTimeTranslate WData htrans t).comp
      (wightmanSpatialTranslate WData htrans a) := by
  unfold wightmanSpatialTranslate wightmanTimeTranslate
  rw [← wightmanTranslate_add, ← wightmanTranslate_add,
      add_comm (euclidSpatialVec a) (euclidTimeVec t)]

omit [Fintype ι] [DecidableEq ι] in
lemma hasCompactSupport_schwartzLorentzCLM (n : ℕ) (A : SL2C)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hf : HasCompactSupport (f : (Fin n → Fin 4 → ℝ) → ℂ)) :
    HasCompactSupport (schwartzLorentzCLM n A f : (Fin n → Fin 4 → ℝ) → ℂ) := by
  have hK : IsCompact
      ((lorentzEquiv n A⁻¹) ''
        tsupport (f : (Fin n → Fin 4 → ℝ) → ℂ)) :=
    hf.isCompact.image (lorentzEquiv n A⁻¹).continuous
  refine HasCompactSupport.of_support_subset_isCompact hK ?_
  intro x hx
  rw [Function.mem_support] at hx
  refine ⟨lorentzEquiv n A x, subset_tsupport _ (Function.mem_support.mpr hx), ?_⟩
  change lorentzActLM n A⁻¹ (lorentzActLM n A x) = x
  rw [lorentzActLM_mul, inv_mul_cancel, lorentzActLM_one]

omit [Fintype ι] [DecidableEq ι] in
noncomputable def compactSchwartzLorentz (n : ℕ) (A : SL2C)
    (f : CompactSchwartz n) : CompactSchwartz n :=
  ⟨schwartzLorentzCLM n A⁻¹ f.val,
   hasCompactSupport_schwartzLorentzCLM n A⁻¹ f.val f.property⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma compactSchwartzLorentz_val (n : ℕ) (A : SL2C) (f : CompactSchwartz n) :
    (compactSchwartzLorentz n A f).val = schwartzLorentzCLM n A⁻¹ f.val := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma compactSchwartzLorentz_one (n : ℕ) (f : CompactSchwartz n) :
    compactSchwartzLorentz n 1 f = f := by
  ext x
  change f.val (lorentzActLM n (1 : SL2C)⁻¹ x) = f.val x
  rw [inv_one, lorentzActLM_one]

omit [Fintype ι] [DecidableEq ι] in
lemma compactSchwartzLorentz_mul (n : ℕ) (A B : SL2C) (f : CompactSchwartz n) :
    compactSchwartzLorentz n (A * B) f =
      compactSchwartzLorentz n A (compactSchwartzLorentz n B f) := by
  ext x
  change f.val (lorentzActLM n (A * B)⁻¹ x) =
    f.val (lorentzActLM n B⁻¹ (lorentzActLM n A⁻¹ x))
  rw [lorentzActLM_mul, _root_.mul_inv_rev]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma compactSchwartzLorentz_fin0 (A : SL2C) (f : CompactSchwartz 0) :
    compactSchwartzLorentz 0 A f = f := by
  ext x
  change f.val (fun i => (lorentzOfSL2C A⁻¹).mulVec (x i)) = f.val x
  congr 1
  ext i
  exact Fin.elim0 i

omit [Fintype ι] [DecidableEq ι] in
lemma compactSchwartzLorentz_translate (n : ℕ) (A : SL2C) (a : Fin 4 → ℝ)
    (f : CompactSchwartz n) :
    compactSchwartzLorentz n A (compactSchwartzTranslate n a f) =
      compactSchwartzTranslate n ((lorentzOfSL2C A).mulVec a)
        (compactSchwartzLorentz n A f) := by
  ext x
  change f.val (fun i => (lorentzOfSL2C A⁻¹).mulVec (x i) - a) =
    f.val (fun i =>
      (lorentzOfSL2C A⁻¹).mulVec (x i - (lorentzOfSL2C A).mulVec a))
  congr 1
  ext i μ
  have h_sub : (lorentzOfSL2C A⁻¹).mulVec (x i - (lorentzOfSL2C A).mulVec a) =
      (lorentzOfSL2C A⁻¹).mulVec (x i) -
        (lorentzOfSL2C A⁻¹).mulVec ((lorentzOfSL2C A).mulVec a) :=
    Matrix.mulVec_sub (lorentzOfSL2C A⁻¹) (x i) ((lorentzOfSL2C A).mulVec a)
  have h_inv : (lorentzOfSL2C A⁻¹).mulVec ((lorentzOfSL2C A).mulVec a) = a := by
    rw [Matrix.mulVec_mulVec, ← lorentzOfSL2C_mul, inv_mul_cancel,
        lorentzOfSL2C_one, Matrix.one_mulVec]
  rw [h_sub, h_inv]

omit [Fintype ι] [DecidableEq ι] in
lemma wightmanConcatSchwartz_lorentz_rel (j k : ℕ) (A : SL2C)
    (f : CompactSchwartz j) (g : CompactSchwartz k)
    (x : Fin (j + k) → Fin 4 → ℝ) :
    wightmanConcatSchwartz j k
      (compactSchwartzLorentz j A f) (compactSchwartzLorentz k A g)
      (fun i => (lorentzOfSL2C A).mulVec (x i)) =
    wightmanConcatSchwartz j k f g x := by
  simp only [wightmanConcatSchwartz_apply, compactSchwartzLorentz_val]
  rw [schwartzLorentz_rel j A f.val (fun i => x (Fin.castAdd k (Fin.rev i))),
      schwartzLorentz_rel k A g.val (fun i => x (Fin.natAdd j i))]

omit [Fintype ι] [DecidableEq ι] in
def WightmanScalarLorentzInvariant (W : WightmanFamily ι) : Prop :=
  ∀ (n : ℕ) (α : Fin n → ι) (A : SL2C)
    (f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
    (∀ x : Fin n → Fin 4 → ℝ,
      f' (fun i => (lorentzOfSL2C A).mulVec (x i)) = f x) →
    W n α f' = W n α f

theorem wightmanScalarLorentzInvariant_of_poincare_rep_eq_one
    (R : HolomorphicLorentzRep ι) {W : WightmanFamily ι}
    (hP : PoincareCovariant R W) (hrep : ∀ A : SL2C, R.rep A = 1) :
    WightmanScalarLorentzInvariant W := by
  intro n α A f f' hf'
  have h_poinc : ∀ x : Fin n → Fin 4 → ℝ,
      f' (fun i => poincareAct 0 A (x i)) = f x := by
    intro x
    dsimp [poincareAct]
    simp only [add_zero]
    exact hf' x
  have h := hP n 0 A f f' h_poinc α
  have h_prod : ∀ β : Fin n → ι,
      (∏ i : Fin n, R.rep A (α i) (β i)) = if α = β then 1 else 0 := by
    intro β
    simp_rw [hrep A]
    by_cases hαβ : α = β
    · subst hαβ
      simp
    · rw [if_neg hαβ]
      obtain ⟨i, hi⟩ : ∃ i, α i ≠ β i := by
        by_contra hc
        push Not at hc
        exact hαβ (funext hc)
      exact Finset.prod_eq_zero (Finset.mem_univ i)
        (by simp [Matrix.one_apply_ne hi])
  simp_rw [h_prod, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true] at h
  exact h

theorem wightmanScalarLorentzInvariant_of_poincare_trivialRep
    {W : WightmanFamily Unit} (hP : PoincareCovariant trivialRep W) :
    WightmanScalarLorentzInvariant W :=
  wightmanScalarLorentzInvariant_of_poincare_rep_eq_one
    trivialRep hP (fun _ => rfl)

omit [Fintype ι] [DecidableEq ι] in
noncomputable def wightmanConfigLorentz (A : SL2C)
    (C : WightmanConfig ι) : WightmanConfig ι :=
  ⟨C.1, (C.2.1, compactSchwartzLorentz C.1 A C.2.2)⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanConfigLorentz_one_apply (C : WightmanConfig ι) :
    wightmanConfigLorentz 1 C = C := by
  rcases C with ⟨n, α, f⟩
  dsimp [wightmanConfigLorentz]
  rw [compactSchwartzLorentz_one]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanConfigLorentz_one :
    wightmanConfigLorentz (ι := ι) 1 = id := by
  ext C : 1
  exact wightmanConfigLorentz_one_apply C

omit [Fintype ι] [DecidableEq ι] in
lemma wightmanConfigLorentz_mul_apply (A B : SL2C) (C : WightmanConfig ι) :
    wightmanConfigLorentz (A * B) C =
      wightmanConfigLorentz A (wightmanConfigLorentz B C) := by
  rcases C with ⟨n, α, f⟩
  dsimp [wightmanConfigLorentz]
  rw [compactSchwartzLorentz_mul]

omit [Fintype ι] [DecidableEq ι] in
lemma wightmanConfigLorentz_mul (A B : SL2C) :
    wightmanConfigLorentz (ι := ι) (A * B) =
      wightmanConfigLorentz A ∘ wightmanConfigLorentz B := by
  ext C : 1
  exact wightmanConfigLorentz_mul_apply A B C

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanConfigLorentz_vacuum (A : SL2C) :
    wightmanConfigLorentz A (wightmanVacuumConfig ι) =
      wightmanVacuumConfig ι := by
  dsimp [wightmanConfigLorentz, wightmanVacuumConfig, wightmanBaseConfig]
  rw [compactSchwartzLorentz_fin0]

omit [Fintype ι] [DecidableEq ι] in
lemma wightmanConfigLorentz_translate (A : SL2C) (a : Fin 4 → ℝ) :
    wightmanConfigLorentz (ι := ι) A ∘ wightmanConfigTranslate a =
      wightmanConfigTranslate ((lorentzOfSL2C A).mulVec a) ∘
        wightmanConfigLorentz A := by
  ext C : 1
  rcases C with ⟨n, α, f⟩
  dsimp [wightmanConfigLorentz, wightmanConfigTranslate]
  rw [compactSchwartzLorentz_translate]

theorem wightmanKernel_scalarLorentz_invariant
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {W : WightmanFamily ι} (hlor : WightmanScalarLorentzInvariant W)
    (A : SL2C) (C₁ C₂ : WightmanConfig ι) :
    wightmanKernel S W
      (wightmanConfigLorentz A C₁) (wightmanConfigLorentz A C₂) =
    wightmanKernel S W C₁ C₂ := by
  rcases C₁ with ⟨j, α, f⟩
  rcases C₂ with ⟨k, α', g⟩
  dsimp [wightmanKernel, wightmanConfigLorentz]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  congr 1
  exact hlor (j + k) (osConcatIdx j k β α') A
    (wightmanConcatSchwartz j k f g)
    (wightmanConcatSchwartz j k
      (compactSchwartzLorentz j A f) (compactSchwartzLorentz k A g))
    (wightmanConcatSchwartz_lorentz_rel j k A f g)

noncomputable def wightmanScalarLorentzLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A : SL2C) :
    WightmanPreHilbertSpace WData →ₗ[ℂ] WightmanPreHilbertSpace WData :=
  wightmanLiftConfigMap WData (wightmanConfigLorentz A)

@[simp]
lemma wightmanScalarLorentzLM_one
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) :
    wightmanScalarLorentzLM WData 1 = LinearMap.id := by
  unfold wightmanScalarLorentzLM
  rw [wightmanConfigLorentz_one, wightmanLiftConfigMap_id]

lemma wightmanScalarLorentzLM_mul
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A B : SL2C) :
    wightmanScalarLorentzLM WData (A * B) =
      (wightmanScalarLorentzLM WData A).comp
        (wightmanScalarLorentzLM WData B) := by
  unfold wightmanScalarLorentzLM
  rw [wightmanConfigLorentz_mul, wightmanLiftConfigMap_comp]

@[simp]
lemma wightmanScalarLorentzLM_vacuumPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A : SL2C) :
    wightmanScalarLorentzLM WData A (wightmanVacuumPre WData) =
      wightmanVacuumPre WData := by
  dsimp [wightmanScalarLorentzLM, wightmanVacuumPre]
  rw [wightmanLiftConfigMap_wightmanBasisPre, wightmanConfigLorentz_vacuum]

theorem inner_wightmanScalarLorentzLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hlor : WightmanScalarLorentzInvariant WData.W)
    (A : SL2C) (Ψ Φ : WightmanPreHilbertSpace WData) :
    ⟪wightmanScalarLorentzLM WData A Ψ,
      wightmanScalarLorentzLM WData A Φ⟫_ℂ = ⟪Ψ, Φ⟫_ℂ := by
  unfold wightmanScalarLorentzLM
  rw [inner_wightmanLiftConfigMap WData
      (wightmanConfigLorentz A) (wightmanConfigLorentz A) Ψ Φ,
      WightmanPreHilbertSpace.inner_def]
  unfold wightmanPreInner
  refine Finsupp.sum_congr (fun C₁ _ => Finsupp.sum_congr (fun C₂ _ => ?_))
  rw [wightmanKernel_scalarLorentz_invariant S hlor A C₁ C₂]

theorem norm_wightmanScalarLorentzLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hlor : WightmanScalarLorentzInvariant WData.W)
    (A : SL2C) (Ψ : WightmanPreHilbertSpace WData) :
    ‖wightmanScalarLorentzLM WData A Ψ‖ = ‖Ψ‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_wightmanScalarLorentzLM WData hlor A Ψ Ψ]

noncomputable def wightmanScalarLorentzPreCLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hlor : WightmanScalarLorentzInvariant WData.W) (A : SL2C) :
    WightmanPreHilbertSpace WData →L[ℂ] WightmanPreHilbertSpace WData :=
  (wightmanScalarLorentzLM WData A).mkContinuous 1 (fun Ψ => by
    rw [one_mul, norm_wightmanScalarLorentzLM WData hlor A Ψ])

noncomputable def wightmanScalarLorentz
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hlor : WightmanScalarLorentzInvariant WData.W) (A : SL2C) :
    WightmanHilbert WData →L[ℂ] WightmanHilbert WData :=
  (wightmanScalarLorentzPreCLM WData hlor A).completion

@[simp]
lemma wightmanScalarLorentz_toWightmanHilbert
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hlor : WightmanScalarLorentzInvariant WData.W) (A : SL2C)
    (Ψ : WightmanPreHilbertSpace WData) :
    wightmanScalarLorentz WData hlor A (toWightmanHilbert WData Ψ) =
      toWightmanHilbert WData (wightmanScalarLorentzLM WData A Ψ) :=
  ContinuousLinearMap.completion_apply_coe
    (wightmanScalarLorentzPreCLM WData hlor A) Ψ

@[simp]
theorem wightmanScalarLorentz_one
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hlor : WightmanScalarLorentzInvariant WData.W) :
    wightmanScalarLorentz WData hlor 1 =
      ContinuousLinearMap.id ℂ (WightmanHilbert WData) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change wightmanScalarLorentz WData hlor 1
      (toWightmanHilbert WData Ψ) = toWightmanHilbert WData Ψ
    rw [wightmanScalarLorentz_toWightmanHilbert,
        wightmanScalarLorentzLM_one, LinearMap.id_apply]

theorem wightmanScalarLorentz_mul
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hlor : WightmanScalarLorentzInvariant WData.W) (A B : SL2C) :
    wightmanScalarLorentz WData hlor (A * B) =
      (wightmanScalarLorentz WData hlor A).comp
        (wightmanScalarLorentz WData hlor B) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change wightmanScalarLorentz WData hlor (A * B)
        (toWightmanHilbert WData Ψ) =
      wightmanScalarLorentz WData hlor A
        (wightmanScalarLorentz WData hlor B (toWightmanHilbert WData Ψ))
    rw [wightmanScalarLorentz_toWightmanHilbert,
        wightmanScalarLorentz_toWightmanHilbert,
        wightmanScalarLorentz_toWightmanHilbert,
        wightmanScalarLorentzLM_mul, LinearMap.comp_apply]

@[simp]
theorem wightmanScalarLorentz_vacuum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hlor : WightmanScalarLorentzInvariant WData.W) (A : SL2C) :
    wightmanScalarLorentz WData hlor A (wightmanVacuum WData) =
      wightmanVacuum WData := by
  dsimp [wightmanVacuum]
  rw [wightmanScalarLorentz_toWightmanHilbert,
      wightmanScalarLorentzLM_vacuumPre]

theorem inner_wightmanScalarLorentz
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hlor : WightmanScalarLorentzInvariant WData.W) (A : SL2C)
    (x y : WightmanHilbert WData) :
    ⟪wightmanScalarLorentz WData hlor A x,
      wightmanScalarLorentz WData hlor A y⟫_ℂ = ⟪x, y⟫_ℂ := by
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ Φ =>
    change ⟪wightmanScalarLorentz WData hlor A (toWightmanHilbert WData Ψ),
        wightmanScalarLorentz WData hlor A (toWightmanHilbert WData Φ)⟫_ℂ =
      ⟪toWightmanHilbert WData Ψ, toWightmanHilbert WData Φ⟫_ℂ
    rw [wightmanScalarLorentz_toWightmanHilbert,
        wightmanScalarLorentz_toWightmanHilbert,
        inner_toWightmanHilbert, inner_toWightmanHilbert,
        inner_wightmanScalarLorentzLM WData hlor A Ψ Φ]

@[simp]
theorem norm_wightmanScalarLorentz
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hlor : WightmanScalarLorentzInvariant WData.W) (A : SL2C)
    (x : WightmanHilbert WData) :
    ‖wightmanScalarLorentz WData hlor A x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_wightmanScalarLorentz WData hlor A x x]

theorem wightmanScalarLorentz_comp_wightmanTranslate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (hlor : WightmanScalarLorentzInvariant WData.W)
    (A : SL2C) (a : Fin 4 → ℝ) :
    (wightmanScalarLorentz WData hlor A).comp
      (wightmanTranslate WData htrans a) =
    (wightmanTranslate WData htrans ((lorentzOfSL2C A).mulVec a)).comp
      (wightmanScalarLorentz WData hlor A) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change wightmanScalarLorentz WData hlor A
        (wightmanTranslate WData htrans a (toWightmanHilbert WData Ψ)) =
      wightmanTranslate WData htrans ((lorentzOfSL2C A).mulVec a)
        (wightmanScalarLorentz WData hlor A (toWightmanHilbert WData Ψ))
    rw [wightmanTranslate_toWightmanHilbert,
        wightmanScalarLorentz_toWightmanHilbert,
        wightmanScalarLorentz_toWightmanHilbert,
        wightmanTranslate_toWightmanHilbert]
    congr 1
    dsimp [wightmanScalarLorentzLM, wightmanTranslateLM]
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
        ← wightmanLiftConfigMap_comp, ← wightmanLiftConfigMap_comp,
        wightmanConfigLorentz_translate]

@[simp]
theorem wightmanBasis_translate_eq_of_zeroMomentumSpectrumCondition
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hspec : ZeroMomentumSpectrumCondition WData.W)
    (a : Fin 4 → ℝ) (A : WightmanConfig ι) :
    wightmanBasis WData (wightmanConfigTranslate a A) =
      wightmanBasis WData A := by
  have h_eq :
      toWightmanHilbert WData
        (wightmanBasisPre WData (wightmanConfigTranslate a A)) =
      toWightmanHilbert WData (wightmanBasisPre WData A) := by
    refine completion_coe_eq_of_inner_eq ?_ ?_ ?_
    · rw [inner_wightmanBasisPre, inner_wightmanBasisPre,
          wightmanKernel_eq_vladimirovKernel_mul_integral S hspec,
          wightmanKernel_eq_vladimirovKernel_mul_integral S hspec,
          integral_wightmanConfigTranslate]
      rfl
    · rw [inner_wightmanBasisPre, inner_wightmanBasisPre,
          wightmanKernel_eq_vladimirovKernel_mul_integral S hspec,
          wightmanKernel_eq_vladimirovKernel_mul_integral S hspec,
          integral_wightmanConfigTranslate]
      rfl
    · rw [inner_wightmanBasisPre, inner_wightmanBasisPre,
          wightmanKernel_eq_vladimirovKernel_mul_integral S hspec,
          wightmanKernel_eq_vladimirovKernel_mul_integral S hspec,
          integral_wightmanConfigTranslate]
      rfl
  exact h_eq

@[simp]
theorem wightmanTranslate_eq_id_of_zeroMomentumSpectrumCondition
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hspec : ZeroMomentumSpectrumCondition WData.W)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 4 → ℝ) :
    wightmanTranslate WData htrans a =
      ContinuousLinearMap.id ℂ (WightmanHilbert WData) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change wightmanTranslate WData htrans a (toWightmanHilbert WData Ψ) =
      toWightmanHilbert WData Ψ
    have h_expand : toWightmanHilbert WData Ψ =
        ∑ A ∈ Ψ.toFinsupp.support, Ψ.toFinsupp A • wightmanBasis WData A := by
      conv_lhs => rw [wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData Ψ]
      rw [map_finsuppSum]
      unfold Finsupp.sum
      refine Finset.sum_congr rfl (fun A _ => (toWightmanHilbert WData).map_smul _ _)
    rw [h_expand, map_sum]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    rw [map_smul, wightmanTranslate_wightmanBasis,
        wightmanBasis_translate_eq_of_zeroMomentumSpectrumCondition WData hspec a A]

@[simp]
theorem osSpatialTranslate_eq_id_of_vladimirov
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) {W : WightmanFamily ι}
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (htrans : OSTranslationInvariant D.𝒮) (b : Fin 3 → ℝ) :
    osSpatialTranslate D htrans b = ContinuousLinearMap.id ℂ (OSHilbert D) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change osSpatialTranslate D htrans b (toOSHilbert D Ψ) = toOSHilbert D Ψ
    have h_expand : toOSHilbert D Ψ =
        ∑ A ∈ Ψ.toFinsupp.support, Ψ.toFinsupp A • osBasis D A := by
      conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D Ψ]
      rw [map_finsuppSum]
      unfold Finsupp.sum
      refine Finset.sum_congr rfl (fun A _ => (toOSHilbert D).map_smul _ _)
    rw [h_expand, map_sum]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    rw [map_smul]
    congr 1
    dsimp [osBasis]
    rw [osSpatialTranslate_toOSHilbert]
    unfold osSpatialTranslateLM
    rw [osLiftConfigMap_osBasisPre]
    change osBasis D (osConfigSpatialShift b A) = osBasis D A
    rw [osBasis_eq_osIndexedBaseConfig_of_vladimirov D hspec h_schw (osConfigSpatialShift b A),
        osBasis_eq_osIndexedBaseConfig_of_vladimirov D hspec h_schw A]
    rfl

@[simp]
theorem osContractionSemigroup_eq_id_of_vladimirov
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) {W : WightmanFamily ι}
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (hcontr : OSContractionCondition D) (τ : ℝ) (hτ : 0 ≤ τ) :
    osContractionSemigroup D hcontr τ hτ =
      ContinuousLinearMap.id ℂ (OSHilbert D) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change osContractionSemigroup D hcontr τ hτ (toOSHilbert D Ψ) =
      toOSHilbert D Ψ
    have h_expand : toOSHilbert D Ψ =
        ∑ A ∈ Ψ.toFinsupp.support, Ψ.toFinsupp A • osBasis D A := by
      conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D Ψ]
      rw [map_finsuppSum]
      unfold Finsupp.sum
      refine Finset.sum_congr rfl (fun A _ => (toOSHilbert D).map_smul _ _)
    rw [h_expand, map_sum]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    rw [map_smul]
    congr 1
    dsimp [osBasis]
    rw [osContractionSemigroup_toOSHilbert]
    unfold osTimeShiftLM
    rw [osLiftConfigMap_osBasisPre]
    change osBasis D (osConfigTimeShift τ hτ A) = osBasis D A
    rw [osBasis_eq_osIndexedBaseConfig_of_vladimirov D hspec h_schw (osConfigTimeShift τ hτ A),
        osBasis_eq_osIndexedBaseConfig_of_vladimirov D hspec h_schw A]
    rfl

theorem vladimirovOSWightmanLinearIsometryEquiv_intertwines_spatialTranslate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (htrans_os : OSTranslationInvariant D.𝒮)
    (htrans_W : WightmanTranslationInvariant
      (wightmanPositiveDataOfOSData D W hspec h_schw).W)
    (b : Fin 3 → ℝ) (x : OSHilbert D) :
    vladimirovOSWightmanLinearIsometryEquiv D W hspec h_schw
      (osSpatialTranslate D htrans_os b x) =
    wightmanSpatialTranslate (wightmanPositiveDataOfOSData D W hspec h_schw)
      htrans_W b
      (vladimirovOSWightmanLinearIsometryEquiv D W hspec h_schw x) := by
  unfold wightmanSpatialTranslate
  rw [osSpatialTranslate_eq_id_of_vladimirov D hspec h_schw htrans_os b,
      wightmanTranslate_eq_id_of_zeroMomentumSpectrumCondition
        (wightmanPositiveDataOfOSData D W hspec h_schw) hspec htrans_W
        (euclidSpatialVec b),
      ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply]

theorem vladimirovOSWightmanLinearIsometryEquiv_intertwines_contraction_timeTranslate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (hcontr : OSContractionCondition D)
    (htrans_W : WightmanTranslationInvariant
      (wightmanPositiveDataOfOSData D W hspec h_schw).W)
    (τ : ℝ) (hτ : 0 ≤ τ) (x : OSHilbert D) :
    vladimirovOSWightmanLinearIsometryEquiv D W hspec h_schw
      (osContractionSemigroup D hcontr τ hτ x) =
    wightmanTimeTranslate (wightmanPositiveDataOfOSData D W hspec h_schw)
      htrans_W τ
      (vladimirovOSWightmanLinearIsometryEquiv D W hspec h_schw x) := by
  unfold wightmanTimeTranslate
  rw [osContractionSemigroup_eq_id_of_vladimirov D hspec h_schw hcontr τ hτ,
      wightmanTranslate_eq_id_of_zeroMomentumSpectrumCondition
        (wightmanPositiveDataOfOSData D W hspec h_schw) hspec htrans_W
        (euclidTimeVec τ),
      ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply]

theorem fourMomentumW_wightmanTranslationInvariant (q : Fin 4 → ℝ) :
    WightmanTranslationInvariant (fourMomentumW q) :=
  wightmanTranslationInvariant_of_tubeTranslationInvariant
    (fourMomentumTubeExtension q) (fourMomentumTubeTranslationInvariant q)

@[simp]
theorem fourMomentumEvenWightmanTerm_translate (q a : Fin 4 → ℝ)
    (A : WightmanConfig Unit) :
    fourMomentumEvenWightmanTerm q (wightmanConfigTranslate a A) =
      fourMomentumEvenWightmanTerm q A := by
  unfold fourMomentumEvenWightmanTerm wightmanConfigTranslate
  dsimp only [compactSchwartzTranslate_val]
  by_cases hn : A.1 % 2 = 0
  · rw [if_pos hn, if_pos hn, minkowskiFourier_schwartzDiagTranslateN,
        sum_alternatingMomentum_of_even A.1 hn q]
    have h0 : minkowskiInner 0 a = 0 := by
      simp [minkowskiInner_explicit]
    rw [h0, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul]
  · rw [if_neg hn, if_neg hn]

@[simp]
theorem fourMomentumOddWightmanTerm_translate (q a : Fin 4 → ℝ)
    (A : WightmanConfig Unit) :
    fourMomentumOddWightmanTerm q (wightmanConfigTranslate a A) =
      Complex.exp (Complex.I * ((minkowskiInner q a : ℝ) : ℂ)) *
        fourMomentumOddWightmanTerm q A := by
  unfold fourMomentumOddWightmanTerm wightmanConfigTranslate
  dsimp only [compactSchwartzTranslate_val]
  by_cases hn : A.1 % 2 = 1
  · rw [if_pos hn, if_pos hn, minkowskiFourier_schwartzDiagTranslateN,
        sum_neg_alternatingMomentum_of_odd A.1 hn q]
    congr 2
    have h_neg : minkowskiInner (-q) a = -minkowskiInner q a := by
      simp [minkowskiInner_explicit]
      ring
    rw [h_neg, Complex.ofReal_neg, mul_neg, neg_neg]
  · rw [if_neg hn, if_neg hn, mul_zero]

theorem wightmanBasis_fourMomentumWightmanData_translate
    (q a : Fin 4 → ℝ) (A : WightmanConfig Unit) :
    wightmanBasis (fourMomentumWightmanData q)
      (wightmanConfigTranslate a A) =
      fourMomentumEvenWightmanTerm q A •
        wightmanVacuum (fourMomentumWightmanData q) +
      (Complex.exp (Complex.I * ((minkowskiInner q a : ℝ) : ℂ)) *
        fourMomentumOddWightmanTerm q A) •
        fourMomentumWightmanOneParticle q := by
  rw [wightmanBasis_fourMomentumWightmanData_eq,
      fourMomentumEvenWightmanTerm_translate,
      fourMomentumOddWightmanTerm_translate]

@[simp]
theorem wightmanTranslate_fourMomentumWightmanOneParticle
    (q a : Fin 4 → ℝ) :
    wightmanTranslate (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) a
      (fourMomentumWightmanOneParticle q) =
    Complex.exp (Complex.I * ((minkowskiInner q a : ℝ) : ℂ)) •
      fourMomentumWightmanOneParticle q := by
  change wightmanTranslate (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) a
      (wightmanBasis (fourMomentumWightmanData q)
        (fourMomentumWightmanOneParticleConfig q)) = _
  rw [wightmanTranslate_wightmanBasis,
      wightmanBasis_fourMomentumWightmanData_translate,
      fourMomentumEvenWightmanTerm_oneParticleConfig,
      fourMomentumOddWightmanTerm_oneParticleConfig,
      zero_smul, zero_add, mul_one]

theorem wightmanTranslate_fourMomentumWightmanData_apply
    (q a : Fin 4 → ℝ) (Φ : WightmanHilbert (fourMomentumWightmanData q)) :
    wightmanTranslate (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) a Φ =
    ⟪wightmanVacuum (fourMomentumWightmanData q), Φ⟫_ℂ •
      wightmanVacuum (fourMomentumWightmanData q) +
    Complex.exp (Complex.I * ((minkowskiInner q a : ℝ) : ℂ)) •
      (⟪fourMomentumWightmanOneParticle q, Φ⟫_ℂ •
        fourMomentumWightmanOneParticle q) := by
  conv_lhs => rw [fourMomentumWightmanHilbert_eq_vacuum_add_oneParticle q Φ]
  rw [map_add, map_smul, map_smul, wightmanTranslate_vacuum,
      wightmanTranslate_fourMomentumWightmanOneParticle,
      smul_smul, mul_comm ⟪fourMomentumWightmanOneParticle q, Φ⟫_ℂ, ← smul_smul]

lemma fourMomentumSpatialPhase_eq_exp_minkowskiInner
    (q : Fin 4 → ℝ) (b : Fin 3 → ℝ) :
    fourMomentumSpatialPhase q b =
      Complex.exp
        (Complex.I * ((minkowskiInner q (euclidSpatialVec b) : ℝ) : ℂ)) := by
  unfold fourMomentumSpatialPhase
  rw [minkowskiInner_explicit]
  congr 1
  simp [minkowskiInnerC, wickEmbed, euclidSpatialVec]
  ring

@[simp]
theorem wightmanSpatialTranslate_fourMomentumWightmanOneParticle
    (q : Fin 4 → ℝ) (b : Fin 3 → ℝ) :
    wightmanSpatialTranslate (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) b
      (fourMomentumWightmanOneParticle q) =
    fourMomentumSpatialPhase q b • fourMomentumWightmanOneParticle q := by
  unfold wightmanSpatialTranslate
  rw [wightmanTranslate_fourMomentumWightmanOneParticle,
      fourMomentumSpatialPhase_eq_exp_minkowskiInner]

theorem fourMomentumOSWightmanLinearIsometryEquiv_intertwines_spatialTranslate
    (q : Fin 4 → ℝ)
    (htrans : OSTranslationInvariant (fourMomentumOSData q).𝒮)
    (b : Fin 3 → ℝ) (Φ : OSHilbert (fourMomentumOSData q)) :
    fourMomentumOSWightmanLinearIsometryEquiv q
      (osSpatialTranslate (fourMomentumOSData q) htrans b Φ) =
    wightmanSpatialTranslate (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) b
      (fourMomentumOSWightmanLinearIsometryEquiv q Φ) := by
  conv_lhs => rw [osSpatialTranslate_fourMomentumOSData_apply q htrans b Φ]
  conv_rhs =>
    rw [fourMomentumHilbert_eq_vacuum_add_oneParticle q Φ]
  rw [map_add, map_smul, map_smul, map_smul,
      map_add, map_smul, map_smul,
      fourMomentumOSWightmanLinearIsometryEquiv_osVacuum,
      fourMomentumOSWightmanLinearIsometryEquiv_oneParticle,
      map_add, map_smul, map_smul,
      wightmanSpatialTranslate_vacuum,
      wightmanSpatialTranslate_fourMomentumWightmanOneParticle,
      smul_smul, smul_smul, mul_comm]

lemma laplaceExp_mul_I_neg_eq_exp_minkowskiInner_euclidTimeVec
    (q : Fin 4 → ℝ) (t : ℝ) :
    laplaceExp (q 0) (Complex.I * ((-t : ℝ) : ℂ)) =
      Complex.exp
        (Complex.I * ((minkowskiInner q (euclidTimeVec t) : ℝ) : ℂ)) := by
  unfold laplaceExp
  rw [minkowskiInner_explicit]
  congr 1
  dsimp [euclidTimeVec]
  push_cast
  ring

theorem fourMomentumOSHolomorphicSemigroup_realTimeUnitary_apply
    {q : Fin 4 → ℝ} (hq0 : 0 ≤ q 0) (t : ℝ)
    (Φ : OSHilbert (fourMomentumOSData q)) :
    (fourMomentumOSHolomorphicSemigroup hq0).realTimeUnitary (-t) Φ =
      ⟪osVacuum (fourMomentumOSData q), Φ⟫_ℂ •
        osVacuum (fourMomentumOSData q) +
      Complex.exp
        (Complex.I * ((minkowskiInner q (euclidTimeVec t) : ℝ) : ℂ)) •
        (⟪fourMomentumOneParticle q, Φ⟫_ℂ • fourMomentumOneParticle q) := by
  change (fourMomentumOSSpectralDecomposition hq0).entireZ
      (Complex.I * ((-t : ℝ) : ℂ)) Φ = _
  rw [OSSpectralDecomposition.entireZ_apply, Fin.sum_univ_two]
  dsimp [fourMomentumOSSpectralDecomposition]
  rw [laplaceExp_zero_left, one_smul,
      laplaceExp_mul_I_neg_eq_exp_minkowskiInner_euclidTimeVec]

theorem fourMomentumOSWightmanLinearIsometryEquiv_intertwines_realTimeUnitary
    {q : Fin 4 → ℝ} (hq0 : 0 ≤ q 0) (t : ℝ)
    (Φ : OSHilbert (fourMomentumOSData q)) :
    fourMomentumOSWightmanLinearIsometryEquiv q
      ((fourMomentumOSHolomorphicSemigroup hq0).realTimeUnitary (-t) Φ) =
    wightmanTimeTranslate (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) t
      (fourMomentumOSWightmanLinearIsometryEquiv q Φ) := by
  rw [fourMomentumOSHolomorphicSemigroup_realTimeUnitary_apply hq0 t Φ]
  conv_rhs =>
    rw [fourMomentumHilbert_eq_vacuum_add_oneParticle q Φ]
  rw [map_add, map_smul, map_smul, map_smul,
      map_add, map_smul, map_smul,
      fourMomentumOSWightmanLinearIsometryEquiv_osVacuum,
      fourMomentumOSWightmanLinearIsometryEquiv_oneParticle,
      wightmanTimeTranslate,
      wightmanTranslate_fourMomentumWightmanData_apply]
  simp [inner_wightmanVacuum_fourMomentumWightmanOneParticle,
    inner_fourMomentumWightmanOneParticle_wightmanVacuum]

namespace OSEuclideanTubeBridge

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

theorem wightmanTranslationInvariant (B : OSEuclideanTubeBridge R S η 𝒮) :
    WightmanTranslationInvariant B.toWightmanPositiveData.W :=
  wightmanTranslationInvariant_of_poincare R B.poincare

noncomputable def wightmanTranslateOp (B : OSEuclideanTubeBridge R S η 𝒮)
    (a : Fin 4 → ℝ) :
    B.WightmanHilbertSpace →L[ℂ] B.WightmanHilbertSpace :=
  wightmanTranslate B.toWightmanPositiveData B.wightmanTranslationInvariant a

end OSEuclideanTubeBridge

namespace ForwardConeOSEuclideanTubeBridge

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

theorem wightmanTranslationInvariant
    (B : ForwardConeOSEuclideanTubeBridge R S η 𝒮) :
    WightmanTranslationInvariant B.toWightmanPositiveData.W :=
  wightmanTranslationInvariant_of_poincare R B.poincare

noncomputable def wightmanTranslateOp
    (B : ForwardConeOSEuclideanTubeBridge R S η 𝒮) (a : Fin 4 → ℝ) :
    B.WightmanHilbertSpace →L[ℂ] B.WightmanHilbertSpace :=
  wightmanTranslate B.toWightmanPositiveData B.wightmanTranslationInvariant a

end ForwardConeOSEuclideanTubeBridge

namespace OSReconstructedWightman

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

theorem wightmanTranslationInvariant (P : OSReconstructedWightman R S η 𝒮) :
    WightmanTranslationInvariant P.toWightmanPositiveData.W :=
  wightmanTranslationInvariant_of_poincare R P.poincare

noncomputable def wightmanTranslateOp (P : OSReconstructedWightman R S η 𝒮)
    (a : Fin 4 → ℝ) :
    P.WightmanHilbertSpace →L[ℂ] P.WightmanHilbertSpace :=
  wightmanTranslate P.toWightmanPositiveData P.wightmanTranslationInvariant a

noncomputable def wightmanSpatialTranslateOp
    (P : OSReconstructedWightman R S η 𝒮) (a : Fin 3 → ℝ) :
    P.WightmanHilbertSpace →L[ℂ] P.WightmanHilbertSpace :=
  wightmanSpatialTranslate P.toWightmanPositiveData
    P.wightmanTranslationInvariant a

noncomputable def wightmanTimeTranslateOp
    (P : OSReconstructedWightman R S η 𝒮) (t : ℝ) :
    P.WightmanHilbertSpace →L[ℂ] P.WightmanHilbertSpace :=
  wightmanTimeTranslate P.toWightmanPositiveData
    P.wightmanTranslationInvariant t

theorem osWightmanLinearIsometryEquiv_intertwines_spatialTranslate
    (P : OSReconstructedWightman R S η 𝒮)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = vladimirovSchwinger P.W n α x)
    (a : Fin 3 → ℝ) (x : P.Hilbert) :
    P.osWightmanLinearIsometryEquiv h_schw
      (osSpatialTranslate P.osData P.osAxioms.os1_translation a x) =
    P.wightmanSpatialTranslateOp a
      (P.osWightmanLinearIsometryEquiv h_schw x) :=
  vladimirovOSWightmanLinearIsometryEquiv_intertwines_spatialTranslate
    P.osData P.W P.spectrum h_schw P.osAxioms.os1_translation
    P.wightmanTranslationInvariant a x

theorem osWightmanLinearIsometryEquiv_intertwines_contraction_timeTranslate
    (P : OSReconstructedWightman R S η 𝒮)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = vladimirovSchwinger P.W n α x)
    (τ : ℝ) (hτ : 0 ≤ τ) (x : P.Hilbert) :
    P.osWightmanLinearIsometryEquiv h_schw
      (osContractionSemigroup P.osData P.contraction τ hτ x) =
    P.wightmanTimeTranslateOp τ
      (P.osWightmanLinearIsometryEquiv h_schw x) :=
  vladimirovOSWightmanLinearIsometryEquiv_intertwines_contraction_timeTranslate
    P.osData P.W P.spectrum h_schw P.contraction
    P.wightmanTranslationInvariant τ hτ x

end OSReconstructedWightman

namespace ForwardConeOSReconstructedWightman

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

theorem wightmanTranslationInvariant
    (P : ForwardConeOSReconstructedWightman R S η 𝒮) :
    WightmanTranslationInvariant P.toWightmanPositiveData.W :=
  wightmanTranslationInvariant_of_poincare R P.poincare

noncomputable def wightmanTranslateOp
    (P : ForwardConeOSReconstructedWightman R S η 𝒮) (a : Fin 4 → ℝ) :
    P.WightmanHilbertSpace →L[ℂ] P.WightmanHilbertSpace :=
  wightmanTranslate P.toWightmanPositiveData P.wightmanTranslationInvariant a

noncomputable def wightmanSpatialTranslateOp
    (P : ForwardConeOSReconstructedWightman R S η 𝒮) (a : Fin 3 → ℝ) :
    P.WightmanHilbertSpace →L[ℂ] P.WightmanHilbertSpace :=
  wightmanSpatialTranslate P.toWightmanPositiveData
    P.wightmanTranslationInvariant a

noncomputable def wightmanTimeTranslateOp
    (P : ForwardConeOSReconstructedWightman R S η 𝒮) (t : ℝ) :
    P.WightmanHilbertSpace →L[ℂ] P.WightmanHilbertSpace :=
  wightmanTimeTranslate P.toWightmanPositiveData
    P.wightmanTranslationInvariant t

@[simp]
theorem wightmanTranslateOp_vacuum
    (P : ForwardConeOSReconstructedWightman R S η 𝒮) (a : Fin 4 → ℝ) :
    P.wightmanTranslateOp a P.wightmanVacuumVec = P.wightmanVacuumVec :=
  wightmanTranslate_vacuum P.toWightmanPositiveData
    P.wightmanTranslationInvariant a

theorem wightmanTranslateOp_add
    (P : ForwardConeOSReconstructedWightman R S η 𝒮) (a b : Fin 4 → ℝ) :
    P.wightmanTranslateOp (a + b) =
      (P.wightmanTranslateOp a).comp (P.wightmanTranslateOp b) :=
  wightmanTranslate_add P.toWightmanPositiveData
    P.wightmanTranslationInvariant a b

theorem inner_wightmanTranslateOp
    (P : ForwardConeOSReconstructedWightman R S η 𝒮) (a : Fin 4 → ℝ)
    (x y : P.WightmanHilbertSpace) :
    ⟪P.wightmanTranslateOp a x, P.wightmanTranslateOp a y⟫_ℂ = ⟪x, y⟫_ℂ :=
  inner_wightmanTranslate P.toWightmanPositiveData
    P.wightmanTranslationInvariant a x y

end ForwardConeOSReconstructedWightman

namespace ForwardConeSpectralFamily

omit [Fintype ι] [DecidableEq ι] in
theorem wightmanTranslationInvariant (F : ForwardConeSpectralFamily ι) :
    WightmanTranslationInvariant F.toWightmanFamily :=
  wightmanTranslationInvariant_of_tubeTranslationInvariant
    F.toTubeExtension F.tubeTranslationInvariant

noncomputable def wightmanTranslateOp (F : ForwardConeSpectralFamily ι)
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (hpos : Positivity S F.toWightmanFamily) (a : Fin 4 → ℝ) :
    WightmanHilbert (F.toWightmanPositiveData S hpos) →L[ℂ]
      WightmanHilbert (F.toWightmanPositiveData S hpos) :=
  wightmanTranslate (F.toWightmanPositiveData S hpos)
    F.wightmanTranslationInvariant a

end ForwardConeSpectralFamily

theorem phase2_wightman_symmetry_bridge_master
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    {q : Fin 4 → ℝ} (hq0 : 0 ≤ q 0) :
    (wightmanTranslate WData htrans 0 =
      ContinuousLinearMap.id ℂ (WightmanHilbert WData)) ∧
    (∀ a b : Fin 4 → ℝ,
      wightmanTranslate WData htrans (a + b) =
        (wightmanTranslate WData htrans a).comp
          (wightmanTranslate WData htrans b)) ∧
    (∀ a : Fin 4 → ℝ,
      wightmanTranslate WData htrans a (wightmanVacuum WData) =
        wightmanVacuum WData) ∧
    (∀ (a : Fin 4 → ℝ) (x y : WightmanHilbert WData),
      ⟪wightmanTranslate WData htrans a x,
        wightmanTranslate WData htrans a y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
    (∀ a : Fin 4 → ℝ,
      wightmanTranslate (fourMomentumWightmanData q)
        (fourMomentumW_wightmanTranslationInvariant q) a
        (fourMomentumWightmanOneParticle q) =
      Complex.exp (Complex.I * ((minkowskiInner q a : ℝ) : ℂ)) •
        fourMomentumWightmanOneParticle q) ∧
    (∀ (b : Fin 3 → ℝ) (Φ : OSHilbert (fourMomentumOSData q)),
      fourMomentumOSWightmanLinearIsometryEquiv q
        (osSpatialTranslate (fourMomentumOSData q)
          (fourMomentumOSTranslationInvariant q) b Φ) =
      wightmanSpatialTranslate (fourMomentumWightmanData q)
        (fourMomentumW_wightmanTranslationInvariant q) b
        (fourMomentumOSWightmanLinearIsometryEquiv q Φ)) ∧
    (∀ (t : ℝ) (Φ : OSHilbert (fourMomentumOSData q)),
      fourMomentumOSWightmanLinearIsometryEquiv q
        ((fourMomentumOSHolomorphicSemigroup hq0).realTimeUnitary (-t) Φ) =
      wightmanTimeTranslate (fourMomentumWightmanData q)
        (fourMomentumW_wightmanTranslationInvariant q) t
        (fourMomentumOSWightmanLinearIsometryEquiv q Φ)) :=
  ⟨wightmanTranslate_zero WData htrans,
   wightmanTranslate_add WData htrans,
   wightmanTranslate_vacuum WData htrans,
   inner_wightmanTranslate WData htrans,
   wightmanTranslate_fourMomentumWightmanOneParticle q,
   fourMomentumOSWightmanLinearIsometryEquiv_intertwines_spatialTranslate
     q (fourMomentumOSTranslationInvariant q),
   fourMomentumOSWightmanLinearIsometryEquiv_intertwines_realTimeUnitary hq0⟩

@[simp]
lemma inner_wightmanVacuumPre_wightmanBasisPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A : WightmanConfig ι) :
    ⟪wightmanVacuumPre WData, wightmanBasisPre WData A⟫_ℂ =
      wightmanKernel S WData.W (wightmanVacuumConfig ι) A :=
  inner_wightmanBasisPre WData (wightmanVacuumConfig ι) A

@[simp]
lemma inner_wightmanBasisPre_wightmanVacuumPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A : WightmanConfig ι) :
    ⟪wightmanBasisPre WData A, wightmanVacuumPre WData⟫_ℂ =
      wightmanKernel S WData.W A (wightmanVacuumConfig ι) :=
  inner_wightmanBasisPre WData A (wightmanVacuumConfig ι)

@[simp]
lemma inner_wightmanVacuumPre_self
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) :
    ⟪wightmanVacuumPre WData, wightmanVacuumPre WData⟫_ℂ =
      wightmanKernel S WData.W (wightmanVacuumConfig ι)
        (wightmanVacuumConfig ι) :=
  inner_wightmanBasisPre WData (wightmanVacuumConfig ι)
    (wightmanVacuumConfig ι)

@[simp]
theorem inner_wightmanVacuum_wightmanBasis
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A : WightmanConfig ι) :
    ⟪wightmanVacuum WData, wightmanBasis WData A⟫_ℂ =
      wightmanKernel S WData.W (wightmanVacuumConfig ι) A := by
  dsimp [wightmanVacuum, wightmanBasis]
  rw [inner_toWightmanHilbert, inner_wightmanVacuumPre_wightmanBasisPre]

@[simp]
theorem inner_wightmanBasis_wightmanVacuum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A : WightmanConfig ι) :
    ⟪wightmanBasis WData A, wightmanVacuum WData⟫_ℂ =
      wightmanKernel S WData.W A (wightmanVacuumConfig ι) := by
  dsimp [wightmanVacuum, wightmanBasis]
  rw [inner_toWightmanHilbert, inner_wightmanBasisPre_wightmanVacuumPre]

@[simp]
theorem inner_wightmanVacuum_self
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) :
    ⟪wightmanVacuum WData, wightmanVacuum WData⟫_ℂ =
      wightmanKernel S WData.W (wightmanVacuumConfig ι)
        (wightmanVacuumConfig ι) := by
  dsimp [wightmanVacuum]
  rw [inner_toWightmanHilbert, inner_wightmanVacuumPre_self]

def WightmanVacuumNormalized {R : HolomorphicLorentzRep ι}
    (S : StarStructure R) (W : WightmanFamily ι) : Prop :=
  wightmanKernel S W (wightmanVacuumConfig ι) (wightmanVacuumConfig ι) = 1

theorem inner_wightmanVacuum_self_of_normalized
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hvac : WightmanVacuumNormalized S WData.W) :
    ⟪wightmanVacuum WData, wightmanVacuum WData⟫_ℂ = 1 := by
  rw [inner_wightmanVacuum_self, hvac]

theorem norm_wightmanVacuum_of_normalized
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hvac : WightmanVacuumNormalized S WData.W) :
    ‖wightmanVacuum WData‖ = 1 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_wightmanVacuum_self_of_normalized WData hvac]
  simp

lemma inner_wightmanPreHilbert_wightmanVacuumPre_left
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanPreHilbertSpace WData) :
    ⟪wightmanVacuumPre WData, Φ⟫_ℂ =
      Φ.toFinsupp.sum (fun B cB =>
        cB * wightmanKernel S WData.W (wightmanVacuumConfig ι) B) := by
  change wightmanPreInner S WData.W
    (Finsupp.single (wightmanVacuumConfig ι) 1) Φ.toFinsupp = _
  unfold wightmanPreInner
  simp

lemma inner_wightmanPreHilbert_wightmanVacuumPre_right
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Ψ : WightmanPreHilbertSpace WData) :
    ⟪Ψ, wightmanVacuumPre WData⟫_ℂ =
      Ψ.toFinsupp.sum (fun A cA =>
        star cA * wightmanKernel S WData.W A (wightmanVacuumConfig ι)) := by
  change wightmanPreInner S WData.W Ψ.toFinsupp
    (Finsupp.single (wightmanVacuumConfig ι) 1) = _
  unfold wightmanPreInner
  refine Finsupp.sum_congr (fun A _ => ?_)
  simp

lemma inner_wightmanVacuumPre_mul_inner_eq_finsupp_sum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (Ψ Φ : WightmanPreHilbertSpace WData) :
    ⟪Ψ, wightmanVacuumPre WData⟫_ℂ * ⟪wightmanVacuumPre WData, Φ⟫_ℂ =
      Ψ.toFinsupp.sum (fun A cA =>
        Φ.toFinsupp.sum (fun B cB =>
          star cA * cB *
            (wightmanKernel S WData.W A (wightmanVacuumConfig ι) *
              wightmanKernel S WData.W (wightmanVacuumConfig ι) B))) := by
  rw [inner_wightmanPreHilbert_wightmanVacuumPre_right,
      inner_wightmanPreHilbert_wightmanVacuumPre_left, Finsupp.sum_mul]
  refine Finsupp.sum_congr (fun A _ => ?_)
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr (fun B _ => ?_)
  ring

def WightmanClusterAlong {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (a : Fin 4 → ℝ) : Prop :=
  ∀ A B : WightmanConfig ι,
    Tendsto
      (fun t : ℝ =>
        wightmanKernel S WData.W A (wightmanConfigTranslate (t • a) B))
      atTop
      (𝓝 (wightmanKernel S WData.W A (wightmanVacuumConfig ι) *
        wightmanKernel S WData.W (wightmanVacuumConfig ι) B))

def WightmanSpatialClusterAlong {R : HolomorphicLorentzRep ι}
    {S : StarStructure R} (WData : WightmanPositiveData R S)
    (a : Fin 3 → ℝ) : Prop :=
  WightmanClusterAlong WData (euclidSpatialVec a)

def WightmanSpatialClusterDecomposition {R : HolomorphicLorentzRep ι}
    {S : StarStructure R} (WData : WightmanPositiveData R S) : Prop :=
  ∀ a : Fin 3 → ℝ, a ≠ 0 → WightmanSpatialClusterAlong WData a

def WightmanSpacelikeClusterDecomposition {R : HolomorphicLorentzRep ι}
    {S : StarStructure R} (WData : WightmanPositiveData R S) : Prop :=
  ∀ a : Fin 4 → ℝ, minkowskiInner a a < 0 → WightmanClusterAlong WData a

def WightmanTimeClusterDecomposition {R : HolomorphicLorentzRep ι}
    {S : StarStructure R} (WData : WightmanPositiveData R S) : Prop :=
  WightmanClusterAlong WData (euclidTimeVec 1)

omit [Fintype ι] [DecidableEq ι] in
lemma minkowskiInner_euclidSpatialVec_self (a : Fin 3 → ℝ) :
    minkowskiInner (euclidSpatialVec a) (euclidSpatialVec a) =
      -(a 0 * a 0 + a 1 * a 1 + a 2 * a 2) := by
  rw [minkowskiInner_explicit]
  change (0 : ℝ) * 0 - a 0 * a 0 - a 1 * a 1 - a 2 * a 2 =
    -(a 0 * a 0 + a 1 * a 1 + a 2 * a 2)
  ring

omit [Fintype ι] [DecidableEq ι] in
lemma minkowskiInner_euclidSpatialVec_self_lt_zero
    {a : Fin 3 → ℝ} (ha : a ≠ 0) :
    minkowskiInner (euclidSpatialVec a) (euclidSpatialVec a) < 0 := by
  rw [minkowskiInner_euclidSpatialVec_self]
  have h_nonneg : 0 ≤ a 0 * a 0 + a 1 * a 1 + a 2 * a 2 :=
    add_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
      (mul_self_nonneg _)
  have h_ne : a 0 * a 0 + a 1 * a 1 + a 2 * a 2 ≠ 0 := by
    intro h0
    apply ha
    ext i
    have h0' : a 0 * a 0 = 0 := by
      nlinarith [mul_self_nonneg (a 0), mul_self_nonneg (a 1),
        mul_self_nonneg (a 2)]
    have h1' : a 1 * a 1 = 0 := by
      nlinarith [mul_self_nonneg (a 0), mul_self_nonneg (a 1),
        mul_self_nonneg (a 2)]
    have h2' : a 2 * a 2 = 0 := by
      nlinarith [mul_self_nonneg (a 0), mul_self_nonneg (a 1),
        mul_self_nonneg (a 2)]
    fin_cases i
    · exact mul_self_eq_zero.mp h0'
    · exact mul_self_eq_zero.mp h1'
    · exact mul_self_eq_zero.mp h2'
  linarith [lt_of_le_of_ne h_nonneg h_ne.symm]

theorem wightmanSpatialClusterDecomposition_of_spacelike
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {WData : WightmanPositiveData R S}
    (h : WightmanSpacelikeClusterDecomposition WData) :
    WightmanSpatialClusterDecomposition WData :=
  fun a ha => h (euclidSpatialVec a)
    (minkowskiInner_euclidSpatialVec_self_lt_zero ha)

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma smul_euclidSpatialVec (t : ℝ) (a : Fin 3 → ℝ) :
    t • euclidSpatialVec a = euclidSpatialVec (t • a) := by
  ext μ
  refine Fin.cases ?_ ?_ μ
  · simp [euclidSpatialVec]
  · intro i
    simp [euclidSpatialVec]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma smul_euclidTimeVec_one (t : ℝ) :
    t • euclidTimeVec 1 = euclidTimeVec t := by
  ext μ
  refine Fin.cases ?_ ?_ μ
  · simp [euclidTimeVec]
  · intro i
    simp [euclidTimeVec]

theorem tendsto_inner_wightmanTranslateLM_atTop
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) {a : Fin 4 → ℝ}
    (hcluster : WightmanClusterAlong WData a)
    (Ψ Φ : WightmanPreHilbertSpace WData) :
    Tendsto
      (fun t : ℝ => ⟪Ψ, wightmanTranslateLM WData (t • a) Φ⟫_ℂ)
      atTop
      (𝓝 (⟪Ψ, wightmanVacuumPre WData⟫_ℂ *
        ⟪wightmanVacuumPre WData, Φ⟫_ℂ)) := by
  have h_eq : (fun t : ℝ => ⟪Ψ, wightmanTranslateLM WData (t • a) Φ⟫_ℂ) =
      fun t : ℝ =>
        Ψ.toFinsupp.sum (fun A cA =>
          Φ.toFinsupp.sum (fun B cB =>
            star cA * cB *
              wightmanKernel S WData.W A
                (wightmanConfigTranslate (t • a) B))) := by
    ext t
    unfold wightmanTranslateLM
    have hR := inner_wightmanLiftConfigMap WData id
      (wightmanConfigTranslate (t • a)) Ψ Φ
    rw [wightmanLiftConfigMap_id, LinearMap.id_apply] at hR
    exact hR
  rw [h_eq, inner_wightmanVacuumPre_mul_inner_eq_finsupp_sum]
  unfold Finsupp.sum
  refine tendsto_finsetSum _ (fun A _ => ?_)
  refine tendsto_finsetSum _ (fun B _ => ?_)
  exact Tendsto.const_mul
    (star (Ψ.toFinsupp A) * Φ.toFinsupp B) (hcluster A B)

theorem tendsto_inner_wightmanCompletion_of_norm_le_one
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (T : ℝ → WightmanHilbert WData →L[ℂ] WightmanHilbert WData)
    (hT_norm : ∀ (t : ℝ) (z : WightmanHilbert WData), ‖T t z‖ ≤ ‖z‖)
    (hT_dense : ∀ Ψ Φ : WightmanPreHilbertSpace WData,
      Tendsto
        (fun t : ℝ =>
          ⟪toWightmanHilbert WData Ψ, T t (toWightmanHilbert WData Φ)⟫_ℂ)
        atTop
        (𝓝 (⟪toWightmanHilbert WData Ψ, wightmanVacuum WData⟫_ℂ *
          ⟪wightmanVacuum WData, toWightmanHilbert WData Φ⟫_ℂ)))
    (x y : WightmanHilbert WData) :
    Tendsto (fun t : ℝ => ⟪x, T t y⟫_ℂ)
      atTop
      (𝓝 (⟪x, wightmanVacuum WData⟫_ℂ * ⟪wightmanVacuum WData, y⟫_ℂ)) := by
  have h_dense : DenseRange (toWightmanHilbert WData) :=
    UniformSpace.Completion.denseRange_coe
  have h_step1 : ∀ Ψ : WightmanPreHilbertSpace WData,
      Tendsto (fun t : ℝ => ⟪toWightmanHilbert WData Ψ, T t y⟫_ℂ)
        atTop
        (𝓝 (⟪toWightmanHilbert WData Ψ, wightmanVacuum WData⟫_ℂ *
          ⟪wightmanVacuum WData, y⟫_ℂ)) := by
    intro Ψ
    apply tendsto_of_forall_pos_exists_approx
    intro δ hδ
    let M : ℝ :=
      max (‖toWightmanHilbert WData Ψ‖)
        (‖toWightmanHilbert WData Ψ‖ *
          ‖wightmanVacuum WData‖ * ‖wightmanVacuum WData‖) + 1
    have hM_pos : 0 < M := by positivity
    obtain ⟨_, ⟨Φ, rfl⟩, hΦ⟩ :=
      Metric.mem_closure_iff.mp (h_dense y) (δ / M) (div_pos hδ hM_pos)
    rw [dist_eq_norm] at hΦ
    refine ⟨fun t =>
        ⟪toWightmanHilbert WData Ψ, T t (toWightmanHilbert WData Φ)⟫_ℂ,
      ⟪toWightmanHilbert WData Ψ, wightmanVacuum WData⟫_ℂ *
        ⟪wightmanVacuum WData, toWightmanHilbert WData Φ⟫_ℂ,
      hT_dense Ψ Φ, fun t => ?_, ?_⟩
    · have h_sub :
          ⟪toWightmanHilbert WData Ψ, T t y⟫_ℂ -
            ⟪toWightmanHilbert WData Ψ, T t (toWightmanHilbert WData Φ)⟫_ℂ =
          ⟪toWightmanHilbert WData Ψ,
            T t (y - toWightmanHilbert WData Φ)⟫_ℂ := by
        rw [← inner_sub_right, map_sub]
      rw [h_sub]
      have h1 :
          ‖⟪toWightmanHilbert WData Ψ,
              T t (y - toWightmanHilbert WData Φ)⟫_ℂ‖ ≤
            ‖toWightmanHilbert WData Ψ‖ *
              ‖y - toWightmanHilbert WData Φ‖ := by
        refine le_trans (norm_inner_le_norm _ _) ?_
        exact mul_le_mul_of_nonneg_left
          (hT_norm t (y - toWightmanHilbert WData Φ)) (norm_nonneg _)
      have h2 : ‖toWightmanHilbert WData Ψ‖ ≤ M := by
        dsimp [M]
        linarith [le_max_left (‖toWightmanHilbert WData Ψ‖)
          (‖toWightmanHilbert WData Ψ‖ *
            ‖wightmanVacuum WData‖ * ‖wightmanVacuum WData‖)]
      have h3 :
          ‖toWightmanHilbert WData Ψ‖ * ‖y - toWightmanHilbert WData Φ‖ ≤
            M * (δ / M) :=
        mul_le_mul h2 hΦ.le (norm_nonneg _) hM_pos.le
      rw [mul_div_cancel₀ _ (ne_of_gt hM_pos)] at h3
      exact le_trans h1 h3
    · have h_sub :
          ⟪toWightmanHilbert WData Ψ, wightmanVacuum WData⟫_ℂ *
            ⟪wightmanVacuum WData, toWightmanHilbert WData Φ⟫_ℂ -
          ⟪toWightmanHilbert WData Ψ, wightmanVacuum WData⟫_ℂ *
            ⟪wightmanVacuum WData, y⟫_ℂ =
          ⟪toWightmanHilbert WData Ψ, wightmanVacuum WData⟫_ℂ *
            ⟪wightmanVacuum WData, toWightmanHilbert WData Φ - y⟫_ℂ := by
        rw [← mul_sub, inner_sub_right]
      rw [h_sub, norm_mul]
      have ha := norm_inner_le_norm (𝕜 := ℂ)
        (toWightmanHilbert WData Ψ) (wightmanVacuum WData)
      have hb := norm_inner_le_norm (𝕜 := ℂ)
        (wightmanVacuum WData) (toWightmanHilbert WData Φ - y)
      rw [norm_sub_rev] at hb
      have h1 :
          ‖⟪toWightmanHilbert WData Ψ, wightmanVacuum WData⟫_ℂ‖ *
            ‖⟪wightmanVacuum WData, toWightmanHilbert WData Φ - y⟫_ℂ‖ ≤
          (‖toWightmanHilbert WData Ψ‖ *
            ‖wightmanVacuum WData‖ * ‖wightmanVacuum WData‖) *
            ‖y - toWightmanHilbert WData Φ‖ := by
        calc ‖⟪toWightmanHilbert WData Ψ, wightmanVacuum WData⟫_ℂ‖ *
            ‖⟪wightmanVacuum WData, toWightmanHilbert WData Φ - y⟫_ℂ‖
          _ ≤ (‖toWightmanHilbert WData Ψ‖ * ‖wightmanVacuum WData‖) *
              (‖wightmanVacuum WData‖ * ‖y - toWightmanHilbert WData Φ‖) :=
            mul_le_mul ha hb (norm_nonneg _) (by positivity)
          _ = (‖toWightmanHilbert WData Ψ‖ *
              ‖wightmanVacuum WData‖ * ‖wightmanVacuum WData‖) *
              ‖y - toWightmanHilbert WData Φ‖ := by
            ring
      have h2 :
          ‖toWightmanHilbert WData Ψ‖ *
            ‖wightmanVacuum WData‖ * ‖wightmanVacuum WData‖ ≤ M := by
        dsimp [M]
        linarith [le_max_right (‖toWightmanHilbert WData Ψ‖)
          (‖toWightmanHilbert WData Ψ‖ *
            ‖wightmanVacuum WData‖ * ‖wightmanVacuum WData‖)]
      have h3 :
          (‖toWightmanHilbert WData Ψ‖ *
            ‖wightmanVacuum WData‖ * ‖wightmanVacuum WData‖) *
            ‖y - toWightmanHilbert WData Φ‖ ≤ M * (δ / M) :=
        mul_le_mul h2 hΦ.le (norm_nonneg _) hM_pos.le
      rw [mul_div_cancel₀ _ (ne_of_gt hM_pos)] at h3
      exact le_trans h1 h3
  apply tendsto_of_forall_pos_exists_approx
  intro δ hδ
  let M : ℝ :=
    max (‖y‖) (‖wightmanVacuum WData‖ * ‖wightmanVacuum WData‖ * ‖y‖) + 1
  have hM_pos : 0 < M := by positivity
  obtain ⟨_, ⟨Ψ, rfl⟩, hΨ⟩ :=
    Metric.mem_closure_iff.mp (h_dense x) (δ / M) (div_pos hδ hM_pos)
  rw [dist_eq_norm] at hΨ
  refine ⟨fun t => ⟪toWightmanHilbert WData Ψ, T t y⟫_ℂ,
    ⟪toWightmanHilbert WData Ψ, wightmanVacuum WData⟫_ℂ *
      ⟪wightmanVacuum WData, y⟫_ℂ,
    h_step1 Ψ, fun t => ?_, ?_⟩
  · have h_sub :
        ⟪x, T t y⟫_ℂ - ⟪toWightmanHilbert WData Ψ, T t y⟫_ℂ =
        ⟪x - toWightmanHilbert WData Ψ, T t y⟫_ℂ :=
      (inner_sub_left _ _ _).symm
    rw [h_sub]
    have h1 :
        ‖⟪x - toWightmanHilbert WData Ψ, T t y⟫_ℂ‖ ≤
          ‖x - toWightmanHilbert WData Ψ‖ * ‖y‖ := by
      refine le_trans (norm_inner_le_norm (𝕜 := ℂ) _ _) ?_
      exact mul_le_mul_of_nonneg_left (hT_norm t y) (norm_nonneg _)
    have h2 : ‖y‖ ≤ M := by
      dsimp [M]
      linarith [le_max_left (‖y‖)
        (‖wightmanVacuum WData‖ * ‖wightmanVacuum WData‖ * ‖y‖)]
    have h3 : ‖x - toWightmanHilbert WData Ψ‖ * ‖y‖ ≤ (δ / M) * M :=
      mul_le_mul hΨ.le h2 (norm_nonneg _) (by positivity)
    rw [div_mul_cancel₀ _ (ne_of_gt hM_pos)] at h3
    exact le_trans h1 h3
  · have h_sub :
        ⟪toWightmanHilbert WData Ψ, wightmanVacuum WData⟫_ℂ *
          ⟪wightmanVacuum WData, y⟫_ℂ -
        ⟪x, wightmanVacuum WData⟫_ℂ * ⟪wightmanVacuum WData, y⟫_ℂ =
        ⟪toWightmanHilbert WData Ψ - x, wightmanVacuum WData⟫_ℂ *
          ⟪wightmanVacuum WData, y⟫_ℂ := by
      rw [← sub_mul, inner_sub_left]
    rw [h_sub, norm_mul]
    have ha := norm_inner_le_norm (𝕜 := ℂ)
      (toWightmanHilbert WData Ψ - x) (wightmanVacuum WData)
    rw [norm_sub_rev] at ha
    have hb := norm_inner_le_norm (𝕜 := ℂ) (wightmanVacuum WData) y
    have h1 :
        ‖⟪toWightmanHilbert WData Ψ - x, wightmanVacuum WData⟫_ℂ‖ *
          ‖⟪wightmanVacuum WData, y⟫_ℂ‖ ≤
        ‖x - toWightmanHilbert WData Ψ‖ *
          (‖wightmanVacuum WData‖ * ‖wightmanVacuum WData‖ * ‖y‖) := by
      calc ‖⟪toWightmanHilbert WData Ψ - x, wightmanVacuum WData⟫_ℂ‖ *
          ‖⟪wightmanVacuum WData, y⟫_ℂ‖
        _ ≤ (‖x - toWightmanHilbert WData Ψ‖ * ‖wightmanVacuum WData‖) *
            (‖wightmanVacuum WData‖ * ‖y‖) :=
          mul_le_mul ha hb (norm_nonneg _) (by positivity)
        _ = ‖x - toWightmanHilbert WData Ψ‖ *
            (‖wightmanVacuum WData‖ * ‖wightmanVacuum WData‖ * ‖y‖) := by
          ring
    have h2 : ‖wightmanVacuum WData‖ * ‖wightmanVacuum WData‖ * ‖y‖ ≤ M := by
      dsimp [M]
      linarith [le_max_right (‖y‖)
        (‖wightmanVacuum WData‖ * ‖wightmanVacuum WData‖ * ‖y‖)]
    have h3 :
        ‖x - toWightmanHilbert WData Ψ‖ *
          (‖wightmanVacuum WData‖ * ‖wightmanVacuum WData‖ * ‖y‖) ≤
        (δ / M) * M :=
      mul_le_mul hΨ.le h2 (by positivity) (by positivity)
    rw [div_mul_cancel₀ _ (ne_of_gt hM_pos)] at h3
    exact le_trans h1 h3

theorem tendsto_inner_wightmanTranslate_atTop
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    {a : Fin 4 → ℝ} (hcluster : WightmanClusterAlong WData a)
    (x y : WightmanHilbert WData) :
    Tendsto
      (fun t : ℝ => ⟪x, wightmanTranslate WData htrans (t • a) y⟫_ℂ)
      atTop
      (𝓝 (⟪x, wightmanVacuum WData⟫_ℂ * ⟪wightmanVacuum WData, y⟫_ℂ)) := by
  refine tendsto_inner_wightmanCompletion_of_norm_le_one WData
    (fun t => wightmanTranslate WData htrans (t • a))
    (fun t z => (norm_wightmanTranslate WData htrans (t • a) z).le)
    (fun Ψ Φ => ?_) x y
  dsimp [wightmanVacuum]
  rw [inner_toWightmanHilbert, inner_toWightmanHilbert]
  have h_eq : (fun t : ℝ =>
      ⟪toWightmanHilbert WData Ψ,
        wightmanTranslate WData htrans (t • a)
          (toWightmanHilbert WData Φ)⟫_ℂ) =
      fun t : ℝ => ⟪Ψ, wightmanTranslateLM WData (t • a) Φ⟫_ℂ := by
    ext t
    rw [wightmanTranslate_toWightmanHilbert, inner_toWightmanHilbert]
  rw [h_eq]
  exact tendsto_inner_wightmanTranslateLM_atTop WData hcluster Ψ Φ

theorem tendsto_inner_wightmanSpatialTranslate_atTop
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    {a : Fin 3 → ℝ} (hcluster : WightmanSpatialClusterAlong WData a)
    (x y : WightmanHilbert WData) :
    Tendsto
      (fun t : ℝ => ⟪x, wightmanSpatialTranslate WData htrans (t • a) y⟫_ℂ)
      atTop
      (𝓝 (⟪x, wightmanVacuum WData⟫_ℂ * ⟪wightmanVacuum WData, y⟫_ℂ)) := by
  have h := tendsto_inner_wightmanTranslate_atTop WData htrans hcluster x y
  have h_eq :
      (fun t : ℝ =>
        ⟪x, wightmanTranslate WData htrans (t • euclidSpatialVec a) y⟫_ℂ) =
      fun t : ℝ => ⟪x, wightmanSpatialTranslate WData htrans (t • a) y⟫_ℂ := by
    ext t
    rw [smul_euclidSpatialVec]
    rfl
  rwa [h_eq] at h

theorem tendsto_inner_wightmanTimeTranslate_atTop
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (hcluster : WightmanTimeClusterDecomposition WData)
    (x y : WightmanHilbert WData) :
    Tendsto
      (fun t : ℝ => ⟪x, wightmanTimeTranslate WData htrans t y⟫_ℂ)
      atTop
      (𝓝 (⟪x, wightmanVacuum WData⟫_ℂ * ⟪wightmanVacuum WData, y⟫_ℂ)) := by
  have h := tendsto_inner_wightmanTranslate_atTop WData htrans hcluster x y
  have h_eq :
      (fun t : ℝ =>
        ⟪x, wightmanTranslate WData htrans (t • euclidTimeVec 1) y⟫_ℂ) =
      fun t : ℝ => ⟪x, wightmanTimeTranslate WData htrans t y⟫_ℂ := by
    ext t
    rw [smul_euclidTimeVec_one]
    rfl
  rwa [h_eq] at h

theorem tendsto_inner_wightmanTranslate_eq_zero_of_inner_wightmanVacuum_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    {a : Fin 4 → ℝ} (hcluster : WightmanClusterAlong WData a)
    (x : WightmanHilbert WData) {y : WightmanHilbert WData}
    (horth : ⟪wightmanVacuum WData, y⟫_ℂ = 0) :
    Tendsto
      (fun t : ℝ => ⟪x, wightmanTranslate WData htrans (t • a) y⟫_ℂ)
      atTop (𝓝 0) := by
  have h := tendsto_inner_wightmanTranslate_atTop WData htrans hcluster x y
  rwa [horth, mul_zero] at h

theorem eq_smul_wightmanVacuum_of_wightmanTranslate_ray_fixed
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    {a : Fin 4 → ℝ} (hcluster : WightmanClusterAlong WData a)
    {Ψ : WightmanHilbert WData}
    (hfixed : ∀ t : ℝ, wightmanTranslate WData htrans (t • a) Ψ = Ψ) :
    Ψ = ⟪wightmanVacuum WData, Ψ⟫_ℂ • wightmanVacuum WData := by
  have h_inner_eq : ∀ x : WightmanHilbert WData,
      ⟪x, Ψ⟫_ℂ = ⟪x, ⟪wightmanVacuum WData, Ψ⟫_ℂ • wightmanVacuum WData⟫_ℂ := by
    intro x
    have h_tendsto :=
      tendsto_inner_wightmanTranslate_atTop WData htrans hcluster x Ψ
    have h_const_fn :
        (fun t : ℝ => ⟪x, wightmanTranslate WData htrans (t • a) Ψ⟫_ℂ) =
        fun _ : ℝ => ⟪x, Ψ⟫_ℂ := by
      ext t
      rw [hfixed t]
    rw [h_const_fn] at h_tendsto
    have h_lim :
        ⟪x, Ψ⟫_ℂ =
          ⟪x, wightmanVacuum WData⟫_ℂ * ⟪wightmanVacuum WData, Ψ⟫_ℂ :=
      tendsto_nhds_unique tendsto_const_nhds h_tendsto
    rw [h_lim, inner_smul_right, mul_comm]
  have h_diff :
      ⟪Ψ - ⟪wightmanVacuum WData, Ψ⟫_ℂ • wightmanVacuum WData,
        Ψ - ⟪wightmanVacuum WData, Ψ⟫_ℂ • wightmanVacuum WData⟫_ℂ = 0 := by
    rw [inner_sub_right,
        h_inner_eq (Ψ - ⟪wightmanVacuum WData, Ψ⟫_ℂ • wightmanVacuum WData),
        sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h_diff)

theorem eq_zero_of_wightmanTranslate_ray_fixed_of_inner_wightmanVacuum_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    {a : Fin 4 → ℝ} (hcluster : WightmanClusterAlong WData a)
    {Ψ : WightmanHilbert WData}
    (hfixed : ∀ t : ℝ, wightmanTranslate WData htrans (t • a) Ψ = Ψ)
    (horth : ⟪wightmanVacuum WData, Ψ⟫_ℂ = 0) :
    Ψ = 0 := by
  rw [eq_smul_wightmanVacuum_of_wightmanTranslate_ray_fixed
      WData htrans hcluster hfixed, horth, zero_smul]

theorem eq_smul_wightmanVacuum_of_wightmanSpatialTranslate_fixed
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    {a : Fin 3 → ℝ} (hcluster : WightmanSpatialClusterAlong WData a)
    {Ψ : WightmanHilbert WData}
    (hfixed : ∀ t : ℝ, wightmanSpatialTranslate WData htrans (t • a) Ψ = Ψ) :
    Ψ = ⟪wightmanVacuum WData, Ψ⟫_ℂ • wightmanVacuum WData := by
  refine eq_smul_wightmanVacuum_of_wightmanTranslate_ray_fixed
    WData htrans hcluster (fun t => ?_)
  rw [smul_euclidSpatialVec]
  exact hfixed t

theorem eq_zero_of_wightmanSpatialTranslate_fixed_of_inner_wightmanVacuum_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    {a : Fin 3 → ℝ} (hcluster : WightmanSpatialClusterAlong WData a)
    {Ψ : WightmanHilbert WData}
    (hfixed : ∀ t : ℝ, wightmanSpatialTranslate WData htrans (t • a) Ψ = Ψ)
    (horth : ⟪wightmanVacuum WData, Ψ⟫_ℂ = 0) :
    Ψ = 0 := by
  rw [eq_smul_wightmanVacuum_of_wightmanSpatialTranslate_fixed
      WData htrans hcluster hfixed, horth, zero_smul]

theorem eq_smul_wightmanVacuum_of_wightmanTimeTranslate_fixed
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (hcluster : WightmanTimeClusterDecomposition WData)
    {Ψ : WightmanHilbert WData}
    (hfixed : ∀ t : ℝ, wightmanTimeTranslate WData htrans t Ψ = Ψ) :
    Ψ = ⟪wightmanVacuum WData, Ψ⟫_ℂ • wightmanVacuum WData := by
  refine eq_smul_wightmanVacuum_of_wightmanTranslate_ray_fixed
    WData htrans hcluster (fun t => ?_)
  rw [smul_euclidTimeVec_one]
  exact hfixed t

theorem eq_zero_of_wightmanTimeTranslate_fixed_of_inner_wightmanVacuum_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (hcluster : WightmanTimeClusterDecomposition WData)
    {Ψ : WightmanHilbert WData}
    (hfixed : ∀ t : ℝ, wightmanTimeTranslate WData htrans t Ψ = Ψ)
    (horth : ⟪wightmanVacuum WData, Ψ⟫_ℂ = 0) :
    Ψ = 0 := by
  rw [eq_smul_wightmanVacuum_of_wightmanTimeTranslate_fixed
      WData htrans hcluster hfixed, horth, zero_smul]

def WightmanVacuumUnique {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) : Prop :=
  ∀ Ψ : WightmanHilbert WData,
    (∀ a : Fin 4 → ℝ, wightmanTranslate WData htrans a Ψ = Ψ) →
      Ψ = ⟪wightmanVacuum WData, Ψ⟫_ℂ • wightmanVacuum WData

def WightmanSpatialVacuumUnique {R : HolomorphicLorentzRep ι}
    {S : StarStructure R} (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) : Prop :=
  ∀ Ψ : WightmanHilbert WData,
    (∀ a : Fin 3 → ℝ, wightmanSpatialTranslate WData htrans a Ψ = Ψ) →
      Ψ = ⟪wightmanVacuum WData, Ψ⟫_ℂ • wightmanVacuum WData

def WightmanTimeVacuumUnique {R : HolomorphicLorentzRep ι}
    {S : StarStructure R} (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) : Prop :=
  ∀ Ψ : WightmanHilbert WData,
    (∀ t : ℝ, wightmanTimeTranslate WData htrans t Ψ = Ψ) →
      Ψ = ⟪wightmanVacuum WData, Ψ⟫_ℂ • wightmanVacuum WData

def OSVacuumUnique {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S)
    (hcontr : OSContractionCondition D) : Prop :=
  ∀ Ψ : OSHilbert D,
    (∀ (τ : ℝ) (hτ : 0 ≤ τ), osContractionSemigroup D hcontr τ hτ Ψ = Ψ) →
      Ψ = ⟪osVacuum D, Ψ⟫_ℂ • osVacuum D

def OSSpatialVacuumUnique {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S)
    (htrans : OSTranslationInvariant D.𝒮) : Prop :=
  ∀ Ψ : OSHilbert D,
    (∀ a : Fin 3 → ℝ, osSpatialTranslate D htrans a Ψ = Ψ) →
      Ψ = ⟪osVacuum D, Ψ⟫_ℂ • osVacuum D

theorem wightmanVacuumUnique_of_clusterAlong
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    {a : Fin 4 → ℝ} (hcluster : WightmanClusterAlong WData a) :
    WightmanVacuumUnique WData htrans :=
  fun _ hfixed =>
    eq_smul_wightmanVacuum_of_wightmanTranslate_ray_fixed
      WData htrans hcluster (fun t => hfixed (t • a))

theorem wightmanSpatialVacuumUnique_of_spatialClusterAlong
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    {a : Fin 3 → ℝ} (hcluster : WightmanSpatialClusterAlong WData a) :
    WightmanSpatialVacuumUnique WData htrans :=
  fun _ hfixed =>
    eq_smul_wightmanVacuum_of_wightmanSpatialTranslate_fixed
      WData htrans hcluster (fun t => hfixed (t • a))

theorem wightmanTimeVacuumUnique_of_timeCluster
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (hcluster : WightmanTimeClusterDecomposition WData) :
    WightmanTimeVacuumUnique WData htrans :=
  fun _ hfixed =>
    eq_smul_wightmanVacuum_of_wightmanTimeTranslate_fixed
      WData htrans hcluster hfixed

theorem wightmanVacuumUnique_of_wightmanSpatialVacuumUnique
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (huniq : WightmanSpatialVacuumUnique WData htrans) :
    WightmanVacuumUnique WData htrans :=
  fun Ψ hfixed => huniq Ψ (fun a => hfixed (euclidSpatialVec a))

theorem wightmanVacuumUnique_of_wightmanTimeVacuumUnique
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (huniq : WightmanTimeVacuumUnique WData htrans) :
    WightmanVacuumUnique WData htrans :=
  fun Ψ hfixed => huniq Ψ (fun t => hfixed (euclidTimeVec t))

theorem osVacuumUnique_of_timeCluster
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S)
    (hcontr : OSContractionCondition D)
    (hcluster : OSTimeClusterDecomposition D) :
    OSVacuumUnique D hcontr :=
  fun _ hfixed =>
    eq_smul_osVacuum_of_osContractionSemigroup_fixed D hcontr hcluster hfixed

theorem osSpatialVacuumUnique_of_spatialClusterAlong
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S)
    (htrans : OSTranslationInvariant D.𝒮)
    {a : Fin 3 → ℝ} (hcluster : OSSpatialClusterAlong D a) :
    OSSpatialVacuumUnique D htrans :=
  fun _ hfixed =>
    eq_smul_osVacuum_of_osSpatialTranslate_fixed
      D htrans hcluster (fun t => hfixed (t • a))

theorem wightmanVacuumNormalized_iff_osVacuumNormalized_of_vladimirov
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x) :
    WightmanVacuumNormalized S W ↔ OSVacuumNormalized D.𝒮 := by
  unfold WightmanVacuumNormalized OSVacuumNormalized
  rw [← osConfigToWightmanConfig_osVacuumConfig,
      wightmanKernel_osConfigToWightmanConfig_eq_osKernel S hspec h_schw,
      ← inner_osBasis D (osVacuumConfig ι) (osVacuumConfig ι)]
  change ⟪osVacuum D, osVacuum D⟫_ℂ = 1 ↔
    D.𝒮 0 Fin.elim0 (euclidOrderedBasePoint 0) = 1
  rw [inner_osVacuum_self]

theorem wightmanKernel_translate_right_of_zeroMomentumSpectrumCondition
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {W : WightmanFamily ι} (hspec : ZeroMomentumSpectrumCondition W)
    (a : Fin 4 → ℝ) (A B : WightmanConfig ι) :
    wightmanKernel S W A (wightmanConfigTranslate a B) =
      wightmanKernel S W A B := by
  rw [wightmanKernel_eq_vladimirovKernel_mul_integral S hspec A
        (wightmanConfigTranslate a B),
      wightmanKernel_eq_vladimirovKernel_mul_integral S hspec A B,
      integral_wightmanConfigTranslate]
  rfl

theorem osKernel_spatialShift_right_of_vladimirov
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {𝒮 : SchwingerFamily ι} {W : WightmanFamily ι}
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = vladimirovSchwinger W n α x)
    (a : Fin 3 → ℝ) (A B : OSConfig ι) :
    osKernel S 𝒮 A (osConfigSpatialShift a B) = osKernel S 𝒮 A B := by
  rw [osKernel_eq_vladimirovKernel_of_schwinger_eq S hspec h_schw A
        (osConfigSpatialShift a B),
      osKernel_eq_vladimirovKernel_of_schwinger_eq S hspec h_schw A B]
  rfl

theorem osKernel_timeShift_right_of_vladimirov
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {𝒮 : SchwingerFamily ι} {W : WightmanFamily ι}
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = vladimirovSchwinger W n α x)
    (τ : ℝ) (hτ : 0 ≤ τ) (A B : OSConfig ι) :
    osKernel S 𝒮 A (osConfigTimeShift τ hτ B) = osKernel S 𝒮 A B := by
  rw [osKernel_eq_vladimirovKernel_of_schwinger_eq S hspec h_schw A
        (osConfigTimeShift τ hτ B),
      osKernel_eq_vladimirovKernel_of_schwinger_eq S hspec h_schw A B]
  rfl

theorem wightmanClusterAlong_iff_osSpatialClusterAlong_of_vladimirov
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (a : Fin 4 → ℝ) (b : Fin 3 → ℝ) :
    WightmanClusterAlong (wightmanPositiveDataOfOSData D W hspec h_schw) a ↔
      OSSpatialClusterAlong D b := by
  refine ⟨fun hW A B => ?_, fun hOS A B => ?_⟩
  · have h_spec :=
      hW (osConfigToWightmanConfig A) (osConfigToWightmanConfig B)
    have h_lhs :
        (fun t : ℝ =>
          wightmanKernel S W (osConfigToWightmanConfig A)
            (wightmanConfigTranslate (t • a) (osConfigToWightmanConfig B))) =
        fun t : ℝ =>
          osKernel S D.𝒮 A (osConfigSpatialShift (t • b) B) := by
      ext t
      rw [wightmanKernel_translate_right_of_zeroMomentumSpectrumCondition
            S hspec,
          wightmanKernel_osConfigToWightmanConfig_eq_osKernel S hspec h_schw,
          osKernel_spatialShift_right_of_vladimirov S hspec h_schw]
    have h_rhs :
        wightmanKernel S W (osConfigToWightmanConfig A)
          (wightmanVacuumConfig ι) *
        wightmanKernel S W (wightmanVacuumConfig ι)
          (osConfigToWightmanConfig B) =
        osKernel S D.𝒮 A (osVacuumConfig ι) *
          osKernel S D.𝒮 (osVacuumConfig ι) B := by
      rw [← osConfigToWightmanConfig_osVacuumConfig,
          wightmanKernel_osConfigToWightmanConfig_eq_osKernel S hspec h_schw,
          wightmanKernel_osConfigToWightmanConfig_eq_osKernel S hspec h_schw]
    rwa [wightmanPositiveDataOfOSData_W, h_lhs, h_rhs] at h_spec
  · have h_base :=
      hOS (osIndexedBaseConfig A.1 A.2.1) (osIndexedBaseConfig B.1 B.2.1)
    have h_const_os :
        (fun t : ℝ =>
          osKernel S D.𝒮 (osIndexedBaseConfig A.1 A.2.1)
            (osConfigSpatialShift (t • b) (osIndexedBaseConfig B.1 B.2.1))) =
        fun _ : ℝ =>
          osKernel S D.𝒮 (osIndexedBaseConfig A.1 A.2.1)
            (osIndexedBaseConfig B.1 B.2.1) := by
      ext t
      exact osKernel_spatialShift_right_of_vladimirov S hspec h_schw (t • b)
        (osIndexedBaseConfig A.1 A.2.1) (osIndexedBaseConfig B.1 B.2.1)
    rw [h_const_os] at h_base
    have h_os_fac :
        osKernel S D.𝒮 (osIndexedBaseConfig A.1 A.2.1)
          (osIndexedBaseConfig B.1 B.2.1) =
        osKernel S D.𝒮 (osIndexedBaseConfig A.1 A.2.1) (osVacuumConfig ι) *
          osKernel S D.𝒮 (osVacuumConfig ι)
            (osIndexedBaseConfig B.1 B.2.1) :=
      tendsto_nhds_unique tendsto_const_nhds h_base
    have h_w_fac :
        (fun t : ℝ =>
          wightmanKernel S (wightmanPositiveDataOfOSData D W hspec h_schw).W A
            (wightmanConfigTranslate (t • a) B)) =
        fun _ : ℝ =>
          wightmanKernel S (wightmanPositiveDataOfOSData D W hspec h_schw).W A
            (wightmanVacuumConfig ι) *
          wightmanKernel S (wightmanPositiveDataOfOSData D W hspec h_schw).W
            (wightmanVacuumConfig ι) B := by
      ext t
      rw [wightmanPositiveDataOfOSData_W,
          wightmanKernel_translate_right_of_zeroMomentumSpectrumCondition
            S hspec,
          wightmanKernel_eq_osKernel_mul_integral S hspec h_schw A B,
          wightmanKernel_eq_osKernel_mul_integral S hspec h_schw A
            (wightmanVacuumConfig ι),
          wightmanKernel_eq_osKernel_mul_integral S hspec h_schw
            (wightmanVacuumConfig ι) B,
          integral_wightmanVacuumConfig, star_one, one_mul, mul_one, h_os_fac]
      change star (∫ y : Fin A.1 → Fin 4 → ℝ, A.2.2.val y) *
          (∫ z : Fin B.1 → Fin 4 → ℝ, B.2.2.val z) *
          (osKernel S D.𝒮 (osIndexedBaseConfig A.1 A.2.1) (osVacuumConfig ι) *
            osKernel S D.𝒮 (osVacuumConfig ι)
              (osIndexedBaseConfig B.1 B.2.1)) =
        star (∫ y : Fin A.1 → Fin 4 → ℝ, A.2.2.val y) *
          osKernel S D.𝒮 (osIndexedBaseConfig A.1 A.2.1) (osVacuumConfig ι) *
          ((∫ z : Fin B.1 → Fin 4 → ℝ, B.2.2.val z) *
            osKernel S D.𝒮 (osVacuumConfig ι)
              (osIndexedBaseConfig B.1 B.2.1))
      ring
    rw [h_w_fac]
    exact tendsto_const_nhds

theorem wightmanClusterAlong_iff_osTimeCluster_of_vladimirov
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (a : Fin 4 → ℝ) :
    WightmanClusterAlong (wightmanPositiveDataOfOSData D W hspec h_schw) a ↔
      OSTimeClusterDecomposition D := by
  rw [wightmanClusterAlong_iff_osSpatialClusterAlong_of_vladimirov
    D W hspec h_schw a 0]
  refine ⟨fun hOS A B => ?_, fun hT A B => ?_⟩
  · have h_spec := hOS A B
    have h_eq :
        (fun τ : ℝ =>
          osKernel S D.𝒮 A
            (osConfigTimeShift (max τ 0) (le_max_right τ 0) B)) =
        fun t : ℝ => osKernel S D.𝒮 A (osConfigSpatialShift (t • 0) B) := by
      ext τ
      rw [osKernel_timeShift_right_of_vladimirov S hspec h_schw,
          osKernel_spatialShift_right_of_vladimirov S hspec h_schw]
    rwa [h_eq]
  · have h_spec := hT A B
    have h_eq :
        (fun t : ℝ => osKernel S D.𝒮 A (osConfigSpatialShift (t • 0) B)) =
        fun τ : ℝ =>
          osKernel S D.𝒮 A
            (osConfigTimeShift (max τ 0) (le_max_right τ 0) B) := by
      ext t
      rw [osKernel_spatialShift_right_of_vladimirov S hspec h_schw,
          osKernel_timeShift_right_of_vladimirov S hspec h_schw]
    rwa [h_eq]

theorem wightmanTimeCluster_iff_osTimeCluster_of_vladimirov
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x) :
    WightmanTimeClusterDecomposition
        (wightmanPositiveDataOfOSData D W hspec h_schw) ↔
      OSTimeClusterDecomposition D :=
  wightmanClusterAlong_iff_osTimeCluster_of_vladimirov
    D W hspec h_schw (euclidTimeVec 1)

theorem wightmanVacuumUnique_iff_osVacuumUnique_of_vladimirov
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (hcontr : OSContractionCondition D)
    (htrans : WightmanTranslationInvariant W) :
    WightmanVacuumUnique
        (wightmanPositiveDataOfOSData D W hspec h_schw) htrans ↔
      OSVacuumUnique D hcontr := by
  let WData := wightmanPositiveDataOfOSData D W hspec h_schw
  let e := vladimirovOSWightmanLinearIsometryEquiv D W hspec h_schw
  refine ⟨fun hW Ψ hfixed => ?_, fun hOS Ψ hfixed => ?_⟩
  · have h_wfixed : ∀ a : Fin 4 → ℝ,
        wightmanTranslate WData htrans a (e Ψ) = e Ψ := by
      intro a
      rw [wightmanTranslate_eq_id_of_zeroMomentumSpectrumCondition
          WData hspec htrans a, ContinuousLinearMap.id_apply]
    have h_eq := hW (e Ψ) h_wfixed
    have h_symm := congrArg e.symm h_eq
    rw [e.symm_apply_apply, map_smul,
        vladimirovOSWightmanLinearIsometryEquiv_symm_wightmanVacuum,
        ← vladimirovOSWightmanLinearIsometryEquiv_osVacuum D W hspec h_schw,
        e.inner_map_map] at h_symm
    exact h_symm
  · have h_osfixed : ∀ (τ : ℝ) (hτ : 0 ≤ τ),
        osContractionSemigroup D hcontr τ hτ (e.symm Ψ) = e.symm Ψ := by
      intro τ hτ
      rw [osContractionSemigroup_eq_id_of_vladimirov D hspec h_schw hcontr τ hτ,
          ContinuousLinearMap.id_apply]
    have h_eq := hOS (e.symm Ψ) h_osfixed
    have h_map := congrArg e h_eq
    rw [e.apply_symm_apply, map_smul,
        vladimirovOSWightmanLinearIsometryEquiv_osVacuum,
        ← vladimirovOSWightmanLinearIsometryEquiv_symm_wightmanVacuum
          D W hspec h_schw,
        e.symm.inner_map_map] at h_map
    exact h_map

theorem wightmanSpatialVacuumUnique_iff_osSpatialVacuumUnique_of_vladimirov
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (hOS : OSTranslationInvariant D.𝒮)
    (hW : WightmanTranslationInvariant W) :
    WightmanSpatialVacuumUnique
        (wightmanPositiveDataOfOSData D W hspec h_schw) hW ↔
      OSSpatialVacuumUnique D hOS := by
  let WData := wightmanPositiveDataOfOSData D W hspec h_schw
  let e := vladimirovOSWightmanLinearIsometryEquiv D W hspec h_schw
  refine ⟨fun hW_uniq Ψ hfixed => ?_, fun hOS_uniq Ψ hfixed => ?_⟩
  · have h_wfixed : ∀ a : Fin 3 → ℝ,
        wightmanSpatialTranslate WData hW a (e Ψ) = e Ψ := by
      intro a
      rw [← vladimirovOSWightmanLinearIsometryEquiv_intertwines_spatialTranslate
            D W hspec h_schw hOS hW a Ψ, hfixed a]
    have h_eq := hW_uniq (e Ψ) h_wfixed
    have h_symm := congrArg e.symm h_eq
    rw [e.symm_apply_apply, map_smul,
        vladimirovOSWightmanLinearIsometryEquiv_symm_wightmanVacuum,
        ← vladimirovOSWightmanLinearIsometryEquiv_osVacuum D W hspec h_schw,
        e.inner_map_map] at h_symm
    exact h_symm
  · have h_osfixed : ∀ a : Fin 3 → ℝ,
        osSpatialTranslate D hOS a (e.symm Ψ) = e.symm Ψ := by
      intro a
      apply e.injective
      rw [vladimirovOSWightmanLinearIsometryEquiv_intertwines_spatialTranslate
            D W hspec h_schw hOS hW a (e.symm Ψ),
          e.apply_symm_apply, hfixed a]
    have h_eq := hOS_uniq (e.symm Ψ) h_osfixed
    have h_map := congrArg e h_eq
    rw [e.apply_symm_apply, map_smul,
        vladimirovOSWightmanLinearIsometryEquiv_osVacuum,
        ← vladimirovOSWightmanLinearIsometryEquiv_symm_wightmanVacuum
          D W hspec h_schw,
        e.symm.inner_map_map] at h_map
    exact h_map

theorem vacWightman_vacuumNormalized
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    WightmanVacuumNormalized S (vacWightmanData R S).W := by
  dsimp [vacWightmanData]
  rw [wightmanVacuumNormalized_iff_osVacuumNormalized_of_vladimirov
    (vacOSData R S) vacW vacZeroMomentumSpectrumCondition
    (fun n α x _ => by rw [vladimirovSchwinger_vacW]; rfl)]
  exact vacS_vacuumNormalized

@[simp]
theorem inner_wightmanVacuum_vacWightmanData_self
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    ⟪wightmanVacuum (vacWightmanData R S),
      wightmanVacuum (vacWightmanData R S)⟫_ℂ = 1 :=
  inner_wightmanVacuum_self_of_normalized (vacWightmanData R S)
    (vacWightman_vacuumNormalized R S)

@[simp]
theorem norm_wightmanVacuum_vacWightmanData
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    ‖wightmanVacuum (vacWightmanData R S)‖ = 1 :=
  norm_wightmanVacuum_of_normalized (vacWightmanData R S)
    (vacWightman_vacuumNormalized R S)

theorem vacWightmanHilbert_eq_smul_wightmanVacuum
    (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (Φ : WightmanHilbert (vacWightmanData R S)) :
    Φ = ⟪wightmanVacuum (vacWightmanData R S), Φ⟫_ℂ •
      wightmanVacuum (vacWightmanData R S) := by
  let e := vacOSWightmanLinearIsometryEquiv R S
  have h_os := vacHilbert_eq_smul_osVacuum R S (e.symm Φ)
  have h_map := congrArg e h_os
  rw [e.apply_symm_apply, map_smul,
      ← e.inner_map_map (osVacuum (vacOSData R S)) (e.symm Φ),
      e.apply_symm_apply, vacOSWightmanLinearIsometryEquiv_osVacuum R S] at h_map
  exact h_map

theorem vacWightmanClusterAlong
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (a : Fin 4 → ℝ) :
    WightmanClusterAlong (vacWightmanData R S) a := by
  dsimp [vacWightmanData]
  rw [wightmanClusterAlong_iff_osTimeCluster_of_vladimirov
    (vacOSData R S) vacW vacZeroMomentumSpectrumCondition
    (fun n α x _ => by rw [vladimirovSchwinger_vacW]; rfl) a]
  exact vacOSTimeCluster R S

theorem vacWightmanVacuumUnique
    (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (htrans : WightmanTranslationInvariant (vacWightmanData R S).W) :
    WightmanVacuumUnique (vacWightmanData R S) htrans :=
  fun Φ _ => vacWightmanHilbert_eq_smul_wightmanVacuum R S Φ

theorem fourMomentumWightman_vacuumNormalized (q : Fin 4 → ℝ) :
    WightmanVacuumNormalized trivialStarStructure
      (fourMomentumWightmanData q).W := by
  unfold WightmanVacuumNormalized
  rw [← inner_wightmanVacuum_self (fourMomentumWightmanData q),
      inner_wightmanVacuum_fourMomentumWightmanData_self]

theorem fourMomentumWightmanOneParticle_ne_zero (q : Fin 4 → ℝ) :
    fourMomentumWightmanOneParticle q ≠ 0 := by
  intro h
  have hn := norm_fourMomentumWightmanOneParticle q
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

theorem wightmanTranslate_fourMomentumWightmanData_fixed_iff
    (q a : Fin 4 → ℝ) (Φ : WightmanHilbert (fourMomentumWightmanData q)) :
    wightmanTranslate (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) a Φ = Φ ↔
      (Complex.exp (Complex.I * ((minkowskiInner q a : ℝ) : ℂ)) - 1) *
        ⟪fourMomentumWightmanOneParticle q, Φ⟫_ℂ = 0 := by
  have h_diff :
      wightmanTranslate (fourMomentumWightmanData q)
          (fourMomentumW_wightmanTranslationInvariant q) a Φ - Φ =
        ((Complex.exp (Complex.I * ((minkowskiInner q a : ℝ) : ℂ)) - 1) *
          ⟪fourMomentumWightmanOneParticle q, Φ⟫_ℂ) •
          fourMomentumWightmanOneParticle q := by
    rw [wightmanTranslate_fourMomentumWightmanData_apply q a Φ]
    conv_lhs =>
      arg 2
      rw [fourMomentumWightmanHilbert_eq_vacuum_add_oneParticle q Φ]
    rw [smul_smul, add_sub_add_left_eq_sub, ← sub_smul, sub_mul, one_mul]
  rw [← sub_eq_zero, h_diff,
      smul_eq_zero_iff_left (fourMomentumWightmanOneParticle_ne_zero q)]

omit [Fintype ι] [DecidableEq ι] in
def minkowskiDualVec (q : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![q 0, -q 1, -q 2, -q 3]

omit [Fintype ι] [DecidableEq ι] in
lemma minkowskiInner_minkowskiDualVec (q : Fin 4 → ℝ) :
    minkowskiInner q (minkowskiDualVec q) =
      q 0 * q 0 + q 1 * q 1 + q 2 * q 2 + q 3 * q 3 := by
  rw [minkowskiInner_explicit]
  change q 0 * q 0 - q 1 * (-q 1) - q 2 * (-q 2) - q 3 * (-q 3) =
    q 0 * q 0 + q 1 * q 1 + q 2 * q 2 + q 3 * q 3
  ring

omit [Fintype ι] [DecidableEq ι] in
lemma minkowskiInner_minkowskiDualVec_ne_zero {q : Fin 4 → ℝ} (hq : q ≠ 0) :
    minkowskiInner q (minkowskiDualVec q) ≠ 0 := by
  rw [minkowskiInner_minkowskiDualVec]
  intro h0
  apply hq
  ext μ
  have h0' : q 0 * q 0 = 0 := by
    nlinarith [mul_self_nonneg (q 0), mul_self_nonneg (q 1),
      mul_self_nonneg (q 2), mul_self_nonneg (q 3)]
  have h1' : q 1 * q 1 = 0 := by
    nlinarith [mul_self_nonneg (q 0), mul_self_nonneg (q 1),
      mul_self_nonneg (q 2), mul_self_nonneg (q 3)]
  have h2' : q 2 * q 2 = 0 := by
    nlinarith [mul_self_nonneg (q 0), mul_self_nonneg (q 1),
      mul_self_nonneg (q 2), mul_self_nonneg (q 3)]
  have h3' : q 3 * q 3 = 0 := by
    nlinarith [mul_self_nonneg (q 0), mul_self_nonneg (q 1),
      mul_self_nonneg (q 2), mul_self_nonneg (q 3)]
  fin_cases μ
  · exact mul_self_eq_zero.mp h0'
  · exact mul_self_eq_zero.mp h1'
  · exact mul_self_eq_zero.mp h2'
  · exact mul_self_eq_zero.mp h3'

omit [Fintype ι] [DecidableEq ι] in
lemma exists_minkowskiInner_eq_pi_of_ne_zero {q : Fin 4 → ℝ} (hq : q ≠ 0) :
    ∃ a : Fin 4 → ℝ, minkowskiInner q a = Real.pi := by
  refine ⟨(Real.pi / minkowskiInner q (minkowskiDualVec q)) •
    minkowskiDualVec q, ?_⟩
  rw [minkowskiInner_smul_right,
      div_mul_cancel₀ _ (minkowskiInner_minkowskiDualVec_ne_zero hq)]

omit [Fintype ι] [DecidableEq ι] in
lemma exp_I_mul_pi_sub_one_ne_zero :
    Complex.exp (Complex.I * (Real.pi : ℂ)) - 1 ≠ 0 := by
  rw [mul_comm, Complex.exp_pi_mul_I]
  norm_num

theorem wightmanVacuumUnique_fourMomentumWightmanData_of_ne_zero
    {q : Fin 4 → ℝ} (hq : q ≠ 0) :
    WightmanVacuumUnique (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) := by
  intro Φ hfixed
  obtain ⟨a, ha⟩ := exists_minkowskiInner_eq_pi_of_ne_zero hq
  have ha_fixed :=
    (wightmanTranslate_fourMomentumWightmanData_fixed_iff q a Φ).mp (hfixed a)
  rw [ha] at ha_fixed
  have h_orth : ⟪fourMomentumWightmanOneParticle q, Φ⟫_ℂ = 0 :=
    (mul_eq_zero.mp ha_fixed).resolve_left exp_I_mul_pi_sub_one_ne_zero
  conv_lhs =>
    rw [fourMomentumWightmanHilbert_eq_vacuum_add_oneParticle q Φ]
  rw [h_orth, zero_smul, add_zero]

theorem not_wightmanVacuumUnique_fourMomentumWightmanData_zero :
    ¬ WightmanVacuumUnique (fourMomentumWightmanData 0)
      (fourMomentumW_wightmanTranslationInvariant 0) := by
  intro huniq
  have hfixed : ∀ a : Fin 4 → ℝ,
      wightmanTranslate (fourMomentumWightmanData 0)
        (fourMomentumW_wightmanTranslationInvariant 0) a
        (fourMomentumWightmanOneParticle 0) =
      fourMomentumWightmanOneParticle 0 := by
    intro a
    rw [wightmanTranslate_fourMomentumWightmanOneParticle]
    have h0 : minkowskiInner (0 : Fin 4 → ℝ) a = 0 := by
      simp [minkowskiInner_explicit]
    rw [h0, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul]
  have h_eq := huniq (fourMomentumWightmanOneParticle 0) hfixed
  rw [inner_wightmanVacuum_fourMomentumWightmanOneParticle, zero_smul] at h_eq
  exact fourMomentumWightmanOneParticle_ne_zero 0 h_eq

theorem wightmanVacuumUnique_fourMomentumWightmanData_iff (q : Fin 4 → ℝ) :
    WightmanVacuumUnique (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) ↔ q ≠ 0 := by
  refine ⟨fun huniq hq0 => ?_, wightmanVacuumUnique_fourMomentumWightmanData_of_ne_zero⟩
  subst hq0
  exact not_wightmanVacuumUnique_fourMomentumWightmanData_zero huniq

theorem wightmanTimeVacuumUnique_fourMomentumWightmanData_iff (q : Fin 4 → ℝ) :
    WightmanTimeVacuumUnique (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) ↔ q 0 ≠ 0 := by
  refine ⟨fun huniq hq0 => ?_, fun hq0 Φ hfixed => ?_⟩
  · have hfixed : ∀ t : ℝ,
        wightmanTimeTranslate (fourMomentumWightmanData q)
          (fourMomentumW_wightmanTranslationInvariant q) t
          (fourMomentumWightmanOneParticle q) =
        fourMomentumWightmanOneParticle q := by
      intro t
      unfold wightmanTimeTranslate
      rw [wightmanTranslate_fourMomentumWightmanOneParticle]
      have h0 : minkowskiInner q (euclidTimeVec t) = 0 := by
        simp [minkowskiInner_explicit, euclidTimeVec, hq0]
      rw [h0, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul]
    have h_eq := huniq (fourMomentumWightmanOneParticle q) hfixed
    rw [inner_wightmanVacuum_fourMomentumWightmanOneParticle, zero_smul] at h_eq
    exact fourMomentumWightmanOneParticle_ne_zero q h_eq
  · have ht := hfixed (Real.pi / q 0)
    unfold wightmanTimeTranslate at ht
    have h_iff :=
      (wightmanTranslate_fourMomentumWightmanData_fixed_iff
        q (euclidTimeVec (Real.pi / q 0)) Φ).mp ht
    have h_inner :
        minkowskiInner q (euclidTimeVec (Real.pi / q 0)) = Real.pi := by
      rw [minkowskiInner_explicit]
      dsimp [euclidTimeVec]
      have h_mul : q 0 * (Real.pi / q 0) = Real.pi :=
        mul_div_cancel₀ Real.pi hq0
      linarith
    rw [h_inner] at h_iff
    have h_orth : ⟪fourMomentumWightmanOneParticle q, Φ⟫_ℂ = 0 :=
      (mul_eq_zero.mp h_iff).resolve_left exp_I_mul_pi_sub_one_ne_zero
    conv_lhs =>
      rw [fourMomentumWightmanHilbert_eq_vacuum_add_oneParticle q Φ]
    rw [h_orth, zero_smul, add_zero]

theorem wightmanTimeVacuumUnique_fourMomentumWightmanData_iff_osTimeCluster
    {q : Fin 4 → ℝ} (hq0 : 0 ≤ q 0) :
    WightmanTimeVacuumUnique (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) ↔
      OSTimeClusterDecomposition (fourMomentumOSData q) := by
  rw [wightmanTimeVacuumUnique_fourMomentumWightmanData_iff,
      osTimeClusterDecomposition_fourMomentumOSData_iff]
  exact ⟨fun hne => lt_of_le_of_ne hq0 hne.symm, ne_of_gt⟩

theorem wightmanVacuumUnique_fourMomentum_iff_osTimeCluster_of_mem_closure_forward_cone
    {q : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone) :
    WightmanVacuumUnique (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) ↔
      OSTimeClusterDecomposition (fourMomentumOSData q) := by
  rw [wightmanVacuumUnique_fourMomentumWightmanData_iff,
      osTimeClusterDecomposition_fourMomentumOSData_iff]
  refine ⟨zero_apply_pos_of_mem_closure_forward_light_cone hq, ?_⟩
  intro hpos h0
  rw [h0] at hpos
  exact lt_irrefl 0 hpos

noncomputable def z2FreeWightmanOneParticle :
    WightmanHilbert z2FreeWightmanData :=
  z2FreeOSWightmanLinearIsometryEquiv z2FreeOneParticle

@[simp]
theorem z2FreeOSWightmanLinearIsometryEquiv_osVacuum :
    z2FreeOSWightmanLinearIsometryEquiv (osVacuum z2FreeOSData) =
      wightmanVacuum z2FreeWightmanData :=
  vladimirovOSWightmanLinearIsometryEquiv_osVacuum z2FreeOSData z2FreeW
    (momentZeroMomentumSpectrumCondition z2FreeCoeff)
    (fun n α x _ => by
      change z2FreeS n α x = vladimirovSchwinger (momentW z2FreeCoeff) n α x
      rw [vladimirovSchwinger_momentW]
      rfl)

@[simp]
theorem inner_wightmanVacuum_z2FreeWightmanOneParticle :
    ⟪wightmanVacuum z2FreeWightmanData, z2FreeWightmanOneParticle⟫_ℂ = 0 := by
  dsimp [z2FreeWightmanOneParticle]
  rw [← z2FreeOSWightmanLinearIsometryEquiv_osVacuum,
      z2FreeOSWightmanLinearIsometryEquiv.inner_map_map,
      inner_osVacuum_z2FreeOneParticle]

@[simp]
theorem norm_z2FreeWightmanOneParticle :
    ‖z2FreeWightmanOneParticle‖ = 1 := by
  dsimp [z2FreeWightmanOneParticle]
  rw [z2FreeOSWightmanLinearIsometryEquiv.norm_map, norm_z2FreeOneParticle]

theorem z2FreeWightmanOneParticle_ne_zero :
    z2FreeWightmanOneParticle ≠ 0 := by
  intro h
  have hn := norm_z2FreeWightmanOneParticle
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

theorem not_wightmanVacuumUnique_z2FreeWightmanData
    (htrans : WightmanTranslationInvariant z2FreeWightmanData.W) :
    ¬ WightmanVacuumUnique z2FreeWightmanData htrans := by
  intro huniq
  have hfixed : ∀ a : Fin 4 → ℝ,
      wightmanTranslate z2FreeWightmanData htrans a
        z2FreeWightmanOneParticle = z2FreeWightmanOneParticle := by
    intro a
    rw [wightmanTranslate_eq_id_of_zeroMomentumSpectrumCondition
        z2FreeWightmanData
        (momentZeroMomentumSpectrumCondition z2FreeCoeff) htrans a,
        ContinuousLinearMap.id_apply]
  have h_eq := huniq z2FreeWightmanOneParticle hfixed
  rw [inner_wightmanVacuum_z2FreeWightmanOneParticle, zero_smul] at h_eq
  exact z2FreeWightmanOneParticle_ne_zero h_eq

namespace OSReconstructedWightman

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

theorem wightmanClusterAlong_iff_osTimeCluster
    (P : OSReconstructedWightman R S η 𝒮)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = vladimirovSchwinger P.W n α x)
    (a : Fin 4 → ℝ) :
    WightmanClusterAlong P.toWightmanPositiveData a ↔
      OSTimeClusterDecomposition P.osData :=
  wightmanClusterAlong_iff_osTimeCluster_of_vladimirov
    P.osData P.W P.spectrum h_schw a

theorem wightmanVacuumUnique_iff_osVacuumUnique
    (P : OSReconstructedWightman R S η 𝒮)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = vladimirovSchwinger P.W n α x) :
    WightmanVacuumUnique P.toWightmanPositiveData
        P.wightmanTranslationInvariant ↔
      OSVacuumUnique P.osData P.contraction :=
  wightmanVacuumUnique_iff_osVacuumUnique_of_vladimirov
    P.osData P.W P.spectrum h_schw P.contraction
    P.wightmanTranslationInvariant

end OSReconstructedWightman

theorem phase3_wightman_cluster_vacuum_bridge_master
    (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (q : Fin 4 → ℝ) :
    (∀ Φ : WightmanHilbert (vacWightmanData R S),
      Φ = ⟪wightmanVacuum (vacWightmanData R S), Φ⟫_ℂ •
        wightmanVacuum (vacWightmanData R S)) ∧
    (∀ a : Fin 4 → ℝ, WightmanClusterAlong (vacWightmanData R S) a) ∧
    (WightmanVacuumUnique (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) ↔ q ≠ 0) ∧
    (WightmanTimeVacuumUnique (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) ↔ q 0 ≠ 0) ∧
    (¬ WightmanVacuumUnique z2FreeWightmanData
      (wightmanTranslationInvariant_of_poincare
        trivialRep (momentPoincareCovariant z2FreeCoeff))) :=
  ⟨vacWightmanHilbert_eq_smul_wightmanVacuum R S,
   vacWightmanClusterAlong R S,
   wightmanVacuumUnique_fourMomentumWightmanData_iff q,
   wightmanTimeVacuumUnique_fourMomentumWightmanData_iff q,
   not_wightmanVacuumUnique_z2FreeWightmanData
     (wightmanTranslationInvariant_of_poincare
       trivialRep (momentPoincareCovariant z2FreeCoeff))⟩

noncomputable def vladimirovSchwartzVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (n : ℕ) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    WightmanHilbert WData :=
  (∫ x : Fin n → Fin 4 → ℝ, f x) •
    wightmanBasis WData (wightmanBaseConfig n α)

@[simp]
lemma vladimirovSchwartzVec_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (n : ℕ) (α : Fin n → ι) :
    vladimirovSchwartzVec WData n α 0 = 0 := by
  unfold vladimirovSchwartzVec
  change (∫ x : Fin n → Fin 4 → ℝ, (0 : ℂ)) •
      wightmanBasis WData (wightmanBaseConfig n α) = 0
  rw [MeasureTheory.integral_zero, zero_smul]

lemma vladimirovSchwartzVec_add
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (n : ℕ) (α : Fin n → ι)
    (f g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    vladimirovSchwartzVec WData n α (f + g) =
      vladimirovSchwartzVec WData n α f +
        vladimirovSchwartzVec WData n α g := by
  unfold vladimirovSchwartzVec
  change (∫ x : Fin n → Fin 4 → ℝ, f x + g x) •
      wightmanBasis WData (wightmanBaseConfig n α) = _
  rw [MeasureTheory.integral_add f.integrable g.integrable, add_smul]

lemma vladimirovSchwartzVec_smul
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (n : ℕ) (α : Fin n → ι) (c : ℂ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    vladimirovSchwartzVec WData n α (c • f) =
      c • vladimirovSchwartzVec WData n α f := by
  unfold vladimirovSchwartzVec
  change (∫ x : Fin n → Fin 4 → ℝ, c * f x) •
      wightmanBasis WData (wightmanBaseConfig n α) = _
  rw [MeasureTheory.integral_const_mul, mul_smul]

@[simp]
lemma vladimirovSchwartzVec_schwartzDiagTranslateN
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (n : ℕ) (α : Fin n → ι)
    (a : Fin 4 → ℝ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    vladimirovSchwartzVec WData n α (schwartzDiagTranslateN n a f) =
      vladimirovSchwartzVec WData n α f := by
  unfold vladimirovSchwartzVec
  rw [integral_schwartzDiagTranslateN]

theorem wightmanTranslate_vladimirovSchwartzVec_of_zeroMomentumSpectrumCondition
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hspec : ZeroMomentumSpectrumCondition WData.W)
    (htrans : WightmanTranslationInvariant WData.W)
    (n : ℕ) (α : Fin n → ι) (a : Fin 4 → ℝ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    wightmanTranslate WData htrans a (vladimirovSchwartzVec WData n α f) =
      vladimirovSchwartzVec WData n α (schwartzDiagTranslateN n a f) := by
  rw [vladimirovSchwartzVec_schwartzDiagTranslateN,
      wightmanTranslate_eq_id_of_zeroMomentumSpectrumCondition
        WData hspec htrans a,
      ContinuousLinearMap.id_apply]

theorem vladimirovSchwartzVec_eq_wightmanBasis_of_osData
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (A : WightmanConfig ι) :
    vladimirovSchwartzVec (wightmanPositiveDataOfOSData D W hspec h_schw)
        A.1 A.2.1 A.2.2.val =
      wightmanBasis (wightmanPositiveDataOfOSData D W hspec h_schw) A :=
  (wightmanBasis_eq_integral_smul_wightmanBaseConfig D W hspec h_schw A).symm

theorem inner_vladimirovSchwartzVec_of_zeroMomentumSpectrumCondition
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hspec : ZeroMomentumSpectrumCondition WData.W)
    (j k : ℕ) (α : Fin j → ι) (α' : Fin k → ι)
    (f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (g : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    ⟪vladimirovSchwartzVec WData j α f,
      vladimirovSchwartzVec WData k α' g⟫_ℂ =
    star (∫ y : Fin j → Fin 4 → ℝ, f y) *
      (∫ z : Fin k → Fin 4 → ℝ, g z) *
      vladimirovKernel S WData.W j k α α' := by
  unfold vladimirovSchwartzVec
  rw [inner_smul_left, inner_smul_right, inner_wightmanBasis,
      wightmanKernel_eq_vladimirovKernel_mul_integral S hspec
        (wightmanBaseConfig j α) (wightmanBaseConfig k α'),
      integral_wightmanBaseConfig, integral_wightmanBaseConfig,
      star_one, one_mul, one_mul, ← Complex.star_def, mul_assoc]
  rfl

theorem inner_vladimirovSchwartzVec_eq_wightman_of_zeroMomentumSpectrumCondition
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hspec : ZeroMomentumSpectrumCondition WData.W)
    (j k : ℕ) (α : Fin j → ι) (α' : Fin k → ι)
    (f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (g : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ)
    (h : SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ)
    (hh : ∀ x : Fin (j + k) → Fin 4 → ℝ,
      h x = (starRingEnd ℂ) (f (fun i => x (Fin.castAdd k (Fin.rev i)))) *
        g (fun i => x (Fin.natAdd j i))) :
    ⟪vladimirovSchwartzVec WData j α f,
      vladimirovSchwartzVec WData k α' g⟫_ℂ =
    ∑ β : Fin j → ι,
      (∏ i : Fin j, S.C (α i) (β i)) *
        WData.W (j + k) (Fin.append (β ∘ Fin.rev) α') h := by
  rw [inner_vladimirovSchwartzVec_of_zeroMomentumSpectrumCondition
      WData hspec j k α α' f g]
  unfold vladimirovKernel
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  have hh_eq :
      (fun x : Fin (j + k) → Fin 4 → ℝ => h x) =
      fun x =>
        ((fun y => (starRingEnd ℂ) (f y))
          (fun i => x (Fin.castAdd k (Fin.rev i)))) *
        ((fun z => g z) (fun i => x (Fin.natAdd j i))) := by
    ext x
    exact hh x
  rw [W_n_eq_vladimirov_H_zero_mul_integral hspec (j + k)
      (Fin.append (β ∘ Fin.rev) α') h,
      hh_eq,
      integral_split_rev_mul j k
        (fun y => (starRingEnd ℂ) (f y)) (fun z => g z),
      integral_conj, ← Complex.star_def]
  change (star (∫ y : Fin j → Fin 4 → ℝ, f y) *
      ∫ z : Fin k → Fin 4 → ℝ, g z) *
      ((∏ i : Fin j, S.C (α i) (β i)) *
        vladimirov_H WData.W (j + k) (osConcatIdx j k β α') 0) =
    (∏ i : Fin j, S.C (α i) (β i)) *
      (vladimirov_H WData.W (j + k) (osConcatIdx j k β α') 0 *
        (star (∫ y : Fin j → Fin 4 → ℝ, f y) *
          ∫ z : Fin k → Fin 4 → ℝ, g z))
  ring

noncomputable def vladimirovBorchersSchwartzVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (N : ℕ)
    (F : ∀ j : ℕ, (Fin j → ι) → SchwartzMap (Fin j → Fin 4 → ℝ) ℂ) :
    WightmanHilbert WData :=
  ∑ j ∈ Finset.range (N + 1), ∑ α : Fin j → ι,
    vladimirovSchwartzVec WData j α (F j α)

theorem inner_vladimirovBorchersSchwartzVec_eq_wightmanSesquilinear
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hspec : ZeroMomentumSpectrumCondition WData.W)
    (N : ℕ)
    (F F' : ∀ j : ℕ, (Fin j → ι) → SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (G : ∀ j k : ℕ, (Fin j → ι) → (Fin k → ι) →
      SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ)
    (hG : ∀ (j k : ℕ) (α : Fin j → ι) (α' : Fin k → ι)
      (x : Fin (j + k) → Fin 4 → ℝ),
      G j k α α' x =
        (starRingEnd ℂ) (F j α (fun i => x (Fin.castAdd k (Fin.rev i)))) *
          F' k α' (fun i => x (Fin.natAdd j i))) :
    ⟪vladimirovBorchersSchwartzVec WData N F,
      vladimirovBorchersSchwartzVec WData N F'⟫_ℂ =
    ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          WData.W (j + k) (Fin.append (β ∘ Fin.rev) α') (G j k α α') := by
  unfold vladimirovBorchersSchwartzVec
  rw [sum_inner]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [sum_inner]
  have h_comm :
      (∑ α : Fin j → ι,
        ⟪vladimirovSchwartzVec WData j α (F j α),
          ∑ k ∈ Finset.range (N + 1), ∑ α' : Fin k → ι,
            vladimirovSchwartzVec WData k α' (F' k α')⟫_ℂ) =
      ∑ k ∈ Finset.range (N + 1), ∑ α : Fin j → ι, ∑ α' : Fin k → ι,
        ⟪vladimirovSchwartzVec WData j α (F j α),
          vladimirovSchwartzVec WData k α' (F' k α')⟫_ℂ := by
    have h_inner : ∀ α : Fin j → ι,
        ⟪vladimirovSchwartzVec WData j α (F j α),
          ∑ k ∈ Finset.range (N + 1), ∑ α' : Fin k → ι,
            vladimirovSchwartzVec WData k α' (F' k α')⟫_ℂ =
        ∑ k ∈ Finset.range (N + 1), ∑ α' : Fin k → ι,
          ⟪vladimirovSchwartzVec WData j α (F j α),
            vladimirovSchwartzVec WData k α' (F' k α')⟫_ℂ := by
      intro α
      rw [inner_sum]
      refine Finset.sum_congr rfl (fun k _ => inner_sum _ _ _)
    simp_rw [h_inner]
    exact Finset.sum_comm
  rw [h_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun α _ => ?_)
  refine Finset.sum_congr rfl (fun α' _ => ?_)
  exact inner_vladimirovSchwartzVec_eq_wightman_of_zeroMomentumSpectrumCondition
    WData hspec j k α α' (F j α) (F' k α') (G j k α α') (hG j k α α')

noncomputable def fourMomentumEvenSchwartzTerm (q : Fin 4 → ℝ) (n : ℕ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) : ℂ :=
  if n % 2 = 0 then minkowskiFourier f (alternatingMomentum n q) else 0

noncomputable def fourMomentumOddSchwartzTerm (q : Fin 4 → ℝ) (n : ℕ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) : ℂ :=
  if n % 2 = 1 then minkowskiFourier f (-alternatingMomentum n q) else 0

@[simp]
lemma fourMomentumEvenSchwartzTerm_compact (q : Fin 4 → ℝ)
    (A : WightmanConfig Unit) :
    fourMomentumEvenSchwartzTerm q A.1 A.2.2.val =
      fourMomentumEvenWightmanTerm q A := rfl

@[simp]
lemma fourMomentumOddSchwartzTerm_compact (q : Fin 4 → ℝ)
    (A : WightmanConfig Unit) :
    fourMomentumOddSchwartzTerm q A.1 A.2.2.val =
      fourMomentumOddWightmanTerm q A := rfl

lemma minkowskiFourier_add_n (n : ℕ)
    (f g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (p : Fin n → Fin 4 → ℝ) :
    minkowskiFourier (f + g) p =
      minkowskiFourier f p + minkowskiFourier g p := by
  rw [← minkowskiFourierEvalTD_apply, ← minkowskiFourierEvalTD_apply,
      ← minkowskiFourierEvalTD_apply, map_add]

lemma minkowskiFourier_smul_n (n : ℕ) (c : ℂ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (p : Fin n → Fin 4 → ℝ) :
    minkowskiFourier (c • f) p = c * minkowskiFourier f p := by
  rw [← minkowskiFourierEvalTD_apply, ← minkowskiFourierEvalTD_apply,
      map_smul, smul_eq_mul]

@[simp]
lemma minkowskiFourier_zero_n (n : ℕ) (p : Fin n → Fin 4 → ℝ) :
    minkowskiFourier (0 : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) p = 0 := by
  rw [← minkowskiFourierEvalTD_apply, map_zero]

lemma fourMomentumEvenSchwartzTerm_add (q : Fin 4 → ℝ) (n : ℕ)
    (f g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    fourMomentumEvenSchwartzTerm q n (f + g) =
      fourMomentumEvenSchwartzTerm q n f +
        fourMomentumEvenSchwartzTerm q n g := by
  unfold fourMomentumEvenSchwartzTerm
  by_cases hn : n % 2 = 0
  · rw [if_pos hn, if_pos hn, if_pos hn, minkowskiFourier_add_n]
  · simp [hn]

lemma fourMomentumOddSchwartzTerm_add (q : Fin 4 → ℝ) (n : ℕ)
    (f g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    fourMomentumOddSchwartzTerm q n (f + g) =
      fourMomentumOddSchwartzTerm q n f +
        fourMomentumOddSchwartzTerm q n g := by
  unfold fourMomentumOddSchwartzTerm
  by_cases hn : n % 2 = 1
  · rw [if_pos hn, if_pos hn, if_pos hn, minkowskiFourier_add_n]
  · simp [hn]

lemma fourMomentumEvenSchwartzTerm_smul (q : Fin 4 → ℝ) (n : ℕ) (c : ℂ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    fourMomentumEvenSchwartzTerm q n (c • f) =
      c * fourMomentumEvenSchwartzTerm q n f := by
  unfold fourMomentumEvenSchwartzTerm
  by_cases hn : n % 2 = 0
  · rw [if_pos hn, if_pos hn, minkowskiFourier_smul_n]
  · simp [hn]

lemma fourMomentumOddSchwartzTerm_smul (q : Fin 4 → ℝ) (n : ℕ) (c : ℂ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    fourMomentumOddSchwartzTerm q n (c • f) =
      c * fourMomentumOddSchwartzTerm q n f := by
  unfold fourMomentumOddSchwartzTerm
  by_cases hn : n % 2 = 1
  · rw [if_pos hn, if_pos hn, minkowskiFourier_smul_n]
  · simp [hn]

@[simp]
lemma fourMomentumEvenSchwartzTerm_translate (q a : Fin 4 → ℝ) (n : ℕ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    fourMomentumEvenSchwartzTerm q n (schwartzDiagTranslateN n a f) =
      fourMomentumEvenSchwartzTerm q n f := by
  unfold fourMomentumEvenSchwartzTerm
  by_cases hn : n % 2 = 0
  · rw [if_pos hn, if_pos hn, minkowskiFourier_schwartzDiagTranslateN,
        sum_alternatingMomentum_of_even n hn q]
    have h0 : minkowskiInner 0 a = 0 := by
      simp [minkowskiInner_explicit]
    rw [h0, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul]
  · rw [if_neg hn, if_neg hn]

@[simp]
lemma fourMomentumOddSchwartzTerm_translate (q a : Fin 4 → ℝ) (n : ℕ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    fourMomentumOddSchwartzTerm q n (schwartzDiagTranslateN n a f) =
      Complex.exp (Complex.I * ((minkowskiInner q a : ℝ) : ℂ)) *
        fourMomentumOddSchwartzTerm q n f := by
  unfold fourMomentumOddSchwartzTerm
  by_cases hn : n % 2 = 1
  · rw [if_pos hn, if_pos hn, minkowskiFourier_schwartzDiagTranslateN,
        sum_neg_alternatingMomentum_of_odd n hn q]
    congr 2
    have h_neg : minkowskiInner (-q) a = -minkowskiInner q a := by
      simp [minkowskiInner_explicit]
      ring
    rw [h_neg, Complex.ofReal_neg, mul_neg, neg_neg]
  · rw [if_neg hn, if_neg hn, mul_zero]

noncomputable def fourMomentumSchwartzVec (q : Fin 4 → ℝ) (n : ℕ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    WightmanHilbert (fourMomentumWightmanData q) :=
  fourMomentumEvenSchwartzTerm q n f •
    wightmanVacuum (fourMomentumWightmanData q) +
  fourMomentumOddSchwartzTerm q n f •
    fourMomentumWightmanOneParticle q

@[simp]
theorem fourMomentumSchwartzVec_compact (q : Fin 4 → ℝ)
    (A : WightmanConfig Unit) :
    fourMomentumSchwartzVec q A.1 A.2.2.val =
      wightmanBasis (fourMomentumWightmanData q) A :=
  (wightmanBasis_fourMomentumWightmanData_eq q A).symm

theorem fourMomentumSchwartzVec_add (q : Fin 4 → ℝ) (n : ℕ)
    (f g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    fourMomentumSchwartzVec q n (f + g) =
      fourMomentumSchwartzVec q n f + fourMomentumSchwartzVec q n g := by
  unfold fourMomentumSchwartzVec
  rw [fourMomentumEvenSchwartzTerm_add, fourMomentumOddSchwartzTerm_add,
      add_smul, add_smul]
  abel

theorem fourMomentumSchwartzVec_smul (q : Fin 4 → ℝ) (n : ℕ) (c : ℂ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    fourMomentumSchwartzVec q n (c • f) =
      c • fourMomentumSchwartzVec q n f := by
  unfold fourMomentumSchwartzVec
  rw [fourMomentumEvenSchwartzTerm_smul, fourMomentumOddSchwartzTerm_smul,
      smul_add, mul_smul, mul_smul]

@[simp]
theorem inner_wightmanVacuum_fourMomentumSchwartzVec (q : Fin 4 → ℝ)
    (n : ℕ) (α : Fin n → Unit) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    ⟪wightmanVacuum (fourMomentumWightmanData q),
      fourMomentumSchwartzVec q n f⟫_ℂ =
    fourMomentumW q n α f := by
  unfold fourMomentumSchwartzVec
  rw [inner_add_right, inner_smul_right, inner_smul_right,
      inner_wightmanVacuum_fourMomentumWightmanData_self,
      inner_wightmanVacuum_fourMomentumWightmanOneParticle,
      mul_one, mul_zero, add_zero, fourMomentumW_apply]
  rfl

@[simp]
theorem inner_fourMomentumWightmanOneParticle_fourMomentumSchwartzVec
    (q : Fin 4 → ℝ) (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    ⟪fourMomentumWightmanOneParticle q,
      fourMomentumSchwartzVec q n f⟫_ℂ =
    fourMomentumOddSchwartzTerm q n f := by
  unfold fourMomentumSchwartzVec
  rw [inner_add_right, inner_smul_right, inner_smul_right,
      inner_fourMomentumWightmanOneParticle_wightmanVacuum,
      inner_fourMomentumWightmanOneParticle_self,
      mul_zero, mul_one, zero_add]

theorem inner_fourMomentumSchwartzVec_eq (q : Fin 4 → ℝ) (j k : ℕ)
    (fj : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (fk : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    ⟪fourMomentumSchwartzVec q j fj, fourMomentumSchwartzVec q k fk⟫_ℂ =
      star (fourMomentumEvenSchwartzTerm q j fj) *
        fourMomentumEvenSchwartzTerm q k fk +
      star (fourMomentumOddSchwartzTerm q j fj) *
        fourMomentumOddSchwartzTerm q k fk := by
  unfold fourMomentumSchwartzVec
  rw [inner_add_left, inner_add_right, inner_add_right,
      inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
      inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
      inner_wightmanVacuum_fourMomentumWightmanData_self,
      inner_wightmanVacuum_fourMomentumWightmanOneParticle,
      inner_fourMomentumWightmanOneParticle_wightmanVacuum,
      inner_fourMomentumWightmanOneParticle_self, ← Complex.star_def]
  simp only [mul_one, mul_zero, add_zero, zero_add]

theorem inner_fourMomentumSchwartzVec_eq_fourMomentumW (q : Fin 4 → ℝ)
    (j k : ℕ)
    (fj : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (fk : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ)
    (g : SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ)
    (hg : ∀ x : Fin (j + k) → Fin 4 → ℝ,
      g x = (starRingEnd ℂ) (fj (fun i => x (Fin.castAdd k (Fin.rev i)))) *
        fk (fun i => x (Fin.natAdd j i)))
    (α : Fin (j + k) → Unit) :
    ⟪fourMomentumSchwartzVec q j fj, fourMomentumSchwartzVec q k fk⟫_ℂ =
      fourMomentumW q (j + k) α g := by
  rw [inner_fourMomentumSchwartzVec_eq,
      fourMomentumW_apply_split_rev_mul q j k fj fk g hg α]
  unfold fourMomentumEvenSchwartzTerm fourMomentumOddSchwartzTerm
  by_cases hj0 : j % 2 = 0 <;> by_cases hk0 : k % 2 = 0
  · simp [hj0, hk0]
  · simp [hj0, hk0]
  · simp [hj0, hk0]
  · have hj1 : j % 2 = 1 := by omega
    have hk1 : k % 2 = 1 := by omega
    simp [hj1, hk1]

theorem wightmanTranslate_fourMomentumSchwartzVec (q a : Fin 4 → ℝ)
    (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    wightmanTranslate (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) a
      (fourMomentumSchwartzVec q n f) =
    fourMomentumSchwartzVec q n (schwartzDiagTranslateN n a f) := by
  unfold fourMomentumSchwartzVec
  rw [map_add, map_smul, map_smul, wightmanTranslate_vacuum,
      wightmanTranslate_fourMomentumWightmanOneParticle,
      fourMomentumEvenSchwartzTerm_translate,
      fourMomentumOddSchwartzTerm_translate,
      smul_smul, mul_comm]

omit [Fintype ι] [DecidableEq ι] in
def compactSchwartzStarFun (j : ℕ) (f : CompactSchwartz j)
    (x : Fin j → Fin 4 → ℝ) : ℂ :=
  (starRingEnd ℂ) (f.val (fun i => x (Fin.rev i)))

omit [Fintype ι] [DecidableEq ι] in
lemma compactSchwartzStarFun_contDiff (j : ℕ) (f : CompactSchwartz j) :
    ContDiff ℝ (⊤ : ℕ∞) (compactSchwartzStarFun j f) := by
  have h_rev : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Fin j → Fin 4 → ℝ => (fun i : Fin j => x (Fin.rev i))) :=
    contDiff_pi.mpr (fun i => contDiff_apply ℝ (Fin 4 → ℝ) (Fin.rev i))
  exact Complex.conjCLE.contDiff.comp (f.val.smooth'.comp h_rev)

omit [Fintype ι] [DecidableEq ι] in
lemma compactSchwartzStarFun_hasCompactSupport (j : ℕ)
    (f : CompactSchwartz j) :
    HasCompactSupport (compactSchwartzStarFun j f) := by
  have h_cont : Continuous
      (fun y : Fin j → Fin 4 → ℝ => (fun i : Fin j => y (Fin.rev i))) :=
    continuous_pi (fun i => continuous_apply (Fin.rev i))
  refine HasCompactSupport.of_support_subset_isCompact
    (f.property.isCompact.image h_cont) ?_
  intro x hx
  rw [Function.mem_support] at hx
  have h_ne : f.val (fun i => x (Fin.rev i)) ≠ 0 := by
    intro h0
    apply hx
    simp [compactSchwartzStarFun, h0]
  refine ⟨fun i => x (Fin.rev i), subset_tsupport _ h_ne, ?_⟩
  ext i μ
  change x (Fin.rev (Fin.rev i)) μ = x i μ
  rw [Fin.rev_rev]

omit [Fintype ι] [DecidableEq ι] in
noncomputable def compactSchwartzStar (j : ℕ) (f : CompactSchwartz j) :
    CompactSchwartz j :=
  ⟨(compactSchwartzStarFun_hasCompactSupport j f).toSchwartzMap
      (compactSchwartzStarFun_contDiff j f),
   compactSchwartzStarFun_hasCompactSupport j f⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma compactSchwartzStar_apply (j : ℕ) (f : CompactSchwartz j)
    (x : Fin j → Fin 4 → ℝ) :
    (compactSchwartzStar j f).val x =
      (starRingEnd ℂ) (f.val (fun i => x (Fin.rev i))) := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma compactSchwartzStar_star (j : ℕ) (f : CompactSchwartz j) :
    compactSchwartzStar j (compactSchwartzStar j f) = f := by
  apply Subtype.ext
  ext x
  simp only [compactSchwartzStar_apply, RingHomCompTriple.comp_apply,
    RingHom.id_apply, Fin.rev_rev]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma compactSchwartzStar_translate (j : ℕ) (a : Fin 4 → ℝ)
    (f : CompactSchwartz j) :
    compactSchwartzStar j (compactSchwartzTranslate j a f) =
      compactSchwartzTranslate j a (compactSchwartzStar j f) := by
  apply Subtype.ext
  ext x
  simp [compactSchwartzStar_apply]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma compactSchwartzStar_lorentz (j : ℕ) (L : SL2C)
    (f : CompactSchwartz j) :
    compactSchwartzStar j (compactSchwartzLorentz j L f) =
      compactSchwartzLorentz j L (compactSchwartzStar j f) := by
  apply Subtype.ext
  ext x
  simp [compactSchwartzStar_apply, schwartzLorentzCLM_apply]

omit [Fintype ι] [DecidableEq ι] in
noncomputable def compactSchwartzTensor (j k : ℕ)
    (f : CompactSchwartz j) (g : CompactSchwartz k) :
    CompactSchwartz (j + k) :=
  ⟨wightmanConcatSchwartz j k (compactSchwartzStar j f) g,
   wightmanConcatFun_hasCompactSupport j k (compactSchwartzStar j f) g⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma compactSchwartzTensor_apply (j k : ℕ)
    (f : CompactSchwartz j) (g : CompactSchwartz k)
    (x : Fin (j + k) → Fin 4 → ℝ) :
    (compactSchwartzTensor j k f g).val x =
      f.val (fun i => x (Fin.castAdd k i)) *
        g.val (fun i => x (Fin.natAdd j i)) := by
  change wightmanConcatSchwartz j k (compactSchwartzStar j f) g x = _
  simp only [wightmanConcatSchwartz_apply, compactSchwartzStar_apply,
    RingHomCompTriple.comp_apply, RingHom.id_apply, Fin.rev_rev]

omit [Fintype ι] [DecidableEq ι] in
lemma wightmanConcatSchwartz_eq_compactSchwartzTensor_star (j k : ℕ)
    (f : CompactSchwartz j) (g : CompactSchwartz k) :
    wightmanConcatSchwartz j k f g =
      (compactSchwartzTensor j k (compactSchwartzStar j f) g).val := by
  ext x
  simp [wightmanConcatSchwartz_apply, compactSchwartzTensor_apply]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma integral_compactSchwartzStar (j : ℕ) (f : CompactSchwartz j) :
    (∫ x : Fin j → Fin 4 → ℝ, (compactSchwartzStar j f).val x) =
      star (∫ x : Fin j → Fin 4 → ℝ, f.val x) := by
  change (∫ x : Fin j → Fin 4 → ℝ,
      (starRingEnd ℂ) (f.val (fun i => x (Fin.rev i)))) = _
  rw [integral_conj, integral_comp_rev, ← Complex.star_def]

omit [Fintype ι] [DecidableEq ι] in
lemma integral_compactSchwartzTensor (j k : ℕ)
    (f : CompactSchwartz j) (g : CompactSchwartz k) :
    (∫ x : Fin (j + k) → Fin 4 → ℝ, (compactSchwartzTensor j k f g).val x) =
      (∫ y : Fin j → Fin 4 → ℝ, f.val y) *
        (∫ z : Fin k → Fin 4 → ℝ, g.val z) := by
  change (∫ x : Fin (j + k) → Fin 4 → ℝ,
      wightmanConcatSchwartz j k (compactSchwartzStar j f) g x) = _
  rw [integral_wightmanConcatSchwartz, integral_compactSchwartzStar, star_star]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma compactSchwartzTensor_translate (j k : ℕ) (a : Fin 4 → ℝ)
    (f : CompactSchwartz j) (g : CompactSchwartz k) :
    compactSchwartzTensor j k
      (compactSchwartzTranslate j a f) (compactSchwartzTranslate k a g) =
      compactSchwartzTranslate (j + k) a (compactSchwartzTensor j k f g) := by
  apply Subtype.ext
  ext x
  simp [compactSchwartzTensor_apply]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma compactSchwartzTensor_lorentz (j k : ℕ) (L : SL2C)
    (f : CompactSchwartz j) (g : CompactSchwartz k) :
    compactSchwartzTensor j k
      (compactSchwartzLorentz j L f) (compactSchwartzLorentz k L g) =
      compactSchwartzLorentz (j + k) L (compactSchwartzTensor j k f g) := by
  apply Subtype.ext
  ext x
  simp [compactSchwartzTensor_apply, schwartzLorentzCLM_apply]

omit [Fintype ι] [DecidableEq ι] in
noncomputable def wightmanConfigMul (A B : WightmanConfig ι) :
    WightmanConfig ι :=
  ⟨A.1 + B.1, (Fin.append A.2.1 B.2.1,
    compactSchwartzTensor A.1 B.1 A.2.2 B.2.2)⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanConfigMul_fst (A B : WightmanConfig ι) :
    (wightmanConfigMul A B).1 = A.1 + B.1 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanConfigMul_snd_fst (A B : WightmanConfig ι) :
    (wightmanConfigMul A B).2.1 = Fin.append A.2.1 B.2.1 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanConfigMul_snd_snd (A B : WightmanConfig ι) :
    (wightmanConfigMul A B).2.2 =
      compactSchwartzTensor A.1 B.1 A.2.2 B.2.2 := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma integral_wightmanConfigMul (A B : WightmanConfig ι) :
    (∫ x : Fin (wightmanConfigMul A B).1 → Fin 4 → ℝ,
      (wightmanConfigMul A B).2.2.val x) =
    (∫ y : Fin A.1 → Fin 4 → ℝ, A.2.2.val y) *
      (∫ z : Fin B.1 → Fin 4 → ℝ, B.2.2.val z) :=
  integral_compactSchwartzTensor A.1 B.1 A.2.2 B.2.2

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanConfigTranslate_wightmanConfigMul (a : Fin 4 → ℝ)
    (A B : WightmanConfig ι) :
    wightmanConfigTranslate a (wightmanConfigMul A B) =
      wightmanConfigMul (wightmanConfigTranslate a A)
        (wightmanConfigTranslate a B) := by
  unfold wightmanConfigTranslate wightmanConfigMul
  dsimp only
  rw [compactSchwartzTensor_translate]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanConfigLorentz_wightmanConfigMul (L : SL2C)
    (A B : WightmanConfig ι) :
    wightmanConfigLorentz L (wightmanConfigMul A B) =
      wightmanConfigMul (wightmanConfigLorentz L A)
        (wightmanConfigLorentz L B) := by
  unfold wightmanConfigLorentz wightmanConfigMul
  dsimp only
  rw [compactSchwartzTensor_lorentz]

omit [Fintype ι] [DecidableEq ι] in
noncomputable def wightmanSingleFieldConfig (α : ι)
    (f : CompactSchwartz 1) : WightmanConfig ι :=
  ⟨1, (fun _ => α, f)⟩

noncomputable def wightmanFieldLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A : WightmanConfig ι) :
    WightmanPreHilbertSpace WData →ₗ[ℂ] WightmanPreHilbertSpace WData :=
  wightmanLiftConfigMap WData (wightmanConfigMul A)

noncomputable def wightmanSingleFieldLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (α : ι) (f : CompactSchwartz 1) :
    WightmanPreHilbertSpace WData →ₗ[ℂ] WightmanPreHilbertSpace WData :=
  wightmanFieldLM WData (wightmanSingleFieldConfig α f)

@[simp]
lemma wightmanFieldLM_wightmanBasisPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A B : WightmanConfig ι) :
    wightmanFieldLM WData A (wightmanBasisPre WData B) =
      wightmanBasisPre WData (wightmanConfigMul A B) :=
  wightmanLiftConfigMap_wightmanBasisPre WData (wightmanConfigMul A) B

@[simp]
lemma wightmanFieldLM_wightmanVacuumPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A : WightmanConfig ι) :
    wightmanFieldLM WData A (wightmanVacuumPre WData) =
      wightmanBasisPre WData (wightmanConfigMul A (wightmanVacuumConfig ι)) :=
  wightmanFieldLM_wightmanBasisPre WData A (wightmanVacuumConfig ι)

@[simp]
lemma wightmanSingleFieldLM_wightmanBasisPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (α : ι) (f : CompactSchwartz 1)
    (B : WightmanConfig ι) :
    wightmanSingleFieldLM WData α f (wightmanBasisPre WData B) =
      wightmanBasisPre WData
        (wightmanConfigMul (wightmanSingleFieldConfig α f) B) :=
  wightmanFieldLM_wightmanBasisPre WData (wightmanSingleFieldConfig α f) B

theorem wightmanTranslateLM_wightmanFieldLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (a : Fin 4 → ℝ)
    (A : WightmanConfig ι) (Ψ : WightmanPreHilbertSpace WData) :
    wightmanTranslateLM WData a (wightmanFieldLM WData A Ψ) =
      wightmanFieldLM WData (wightmanConfigTranslate a A)
        (wightmanTranslateLM WData a Ψ) := by
  unfold wightmanTranslateLM wightmanFieldLM
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
      ← wightmanLiftConfigMap_comp, ← wightmanLiftConfigMap_comp]
  congr 2

theorem wightmanScalarLorentzLM_wightmanFieldLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (L : SL2C)
    (A : WightmanConfig ι) (Ψ : WightmanPreHilbertSpace WData) :
    wightmanScalarLorentzLM WData L (wightmanFieldLM WData A Ψ) =
      wightmanFieldLM WData (wightmanConfigLorentz L A)
        (wightmanScalarLorentzLM WData L Ψ) := by
  unfold wightmanScalarLorentzLM wightmanFieldLM
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
      ← wightmanLiftConfigMap_comp, ← wightmanLiftConfigMap_comp]
  congr 2

theorem wightmanTranslateLM_wightmanScalarLorentzLM_wightmanFieldLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (a : Fin 4 → ℝ) (L : SL2C)
    (A : WightmanConfig ι) (Ψ : WightmanPreHilbertSpace WData) :
    wightmanTranslateLM WData a
      (wightmanScalarLorentzLM WData L (wightmanFieldLM WData A Ψ)) =
    wightmanFieldLM WData
      (wightmanConfigTranslate a (wightmanConfigLorentz L A))
      (wightmanTranslateLM WData a
        (wightmanScalarLorentzLM WData L Ψ)) := by
  rw [wightmanScalarLorentzLM_wightmanFieldLM,
      wightmanTranslateLM_wightmanFieldLM]

theorem wightmanBasis_wightmanConfigMul_of_osData
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (A B : WightmanConfig ι) :
    wightmanBasis (wightmanPositiveDataOfOSData D W hspec h_schw)
        (wightmanConfigMul A B) =
      ((∫ y : Fin A.1 → Fin 4 → ℝ, A.2.2.val y) *
        (∫ z : Fin B.1 → Fin 4 → ℝ, B.2.2.val z)) •
        wightmanBasis (wightmanPositiveDataOfOSData D W hspec h_schw)
          (wightmanBaseConfig (A.1 + B.1) (Fin.append A.2.1 B.2.1)) := by
  rw [wightmanBasis_eq_integral_smul_wightmanBaseConfig,
      integral_wightmanConfigMul]
  rfl

theorem toWightmanHilbert_wightmanFieldLM_wightmanVacuumPre_of_osData
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (A : WightmanConfig ι) :
    toWightmanHilbert (wightmanPositiveDataOfOSData D W hspec h_schw)
        (wightmanFieldLM (wightmanPositiveDataOfOSData D W hspec h_schw) A
          (wightmanVacuumPre (wightmanPositiveDataOfOSData D W hspec h_schw))) =
      (∫ y : Fin A.1 → Fin 4 → ℝ, A.2.2.val y) •
        wightmanBasis (wightmanPositiveDataOfOSData D W hspec h_schw)
          (wightmanBaseConfig (A.1 + 0)
            (Fin.append A.2.1 (wightmanVacuumConfig ι).2.1)) := by
  rw [wightmanFieldLM_wightmanVacuumPre]
  change wightmanBasis (wightmanPositiveDataOfOSData D W hspec h_schw)
      (wightmanConfigMul A (wightmanVacuumConfig ι)) = _
  rw [wightmanBasis_wightmanConfigMul_of_osData,
      integral_wightmanVacuumConfig, mul_one]
  rfl

noncomputable def wightmanCyclicSubmodule
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) :
    Submodule ℂ (WightmanHilbert WData) :=
  Submodule.span ℂ (Set.range (wightmanBasis WData))

def WightmanVacuumCyclic
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) : Prop :=
  Dense (wightmanCyclicSubmodule WData : Set (WightmanHilbert WData))

lemma wightmanBasis_mem_wightmanCyclicSubmodule
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A : WightmanConfig ι) :
    wightmanBasis WData A ∈ wightmanCyclicSubmodule WData :=
  Submodule.subset_span (Set.mem_range_self A)

lemma wightmanVacuum_mem_wightmanCyclicSubmodule
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) :
    wightmanVacuum WData ∈ wightmanCyclicSubmodule WData :=
  wightmanBasis_mem_wightmanCyclicSubmodule WData (wightmanVacuumConfig ι)

lemma toWightmanHilbert_mem_wightmanCyclicSubmodule
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (Ψ : WightmanPreHilbertSpace WData) :
    toWightmanHilbert WData Ψ ∈ wightmanCyclicSubmodule WData := by
  have h_expand : toWightmanHilbert WData Ψ =
      ∑ A ∈ Ψ.toFinsupp.support,
        Ψ.toFinsupp A • wightmanBasis WData A := by
    conv_lhs => rw [wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData Ψ]
    rw [map_finsuppSum]
    unfold Finsupp.sum
    refine Finset.sum_congr rfl (fun A _ => (toWightmanHilbert WData).map_smul _ _)
  rw [h_expand]
  exact Submodule.sum_mem (wightmanCyclicSubmodule WData) (fun A _ =>
    Submodule.smul_mem (wightmanCyclicSubmodule WData) (Ψ.toFinsupp A)
      (wightmanBasis_mem_wightmanCyclicSubmodule WData A))

theorem wightmanVacuumCyclic
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) :
    WightmanVacuumCyclic WData := by
  unfold WightmanVacuumCyclic
  have h_dense : DenseRange (toWightmanHilbert WData) :=
    UniformSpace.Completion.denseRange_coe
  refine Dense.mono ?_ h_dense
  rintro x ⟨Ψ, rfl⟩
  exact toWightmanHilbert_mem_wightmanCyclicSubmodule WData Ψ

theorem eq_zero_of_inner_wightmanBasis_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    {Φ : WightmanHilbert WData}
    (horth : ∀ A : WightmanConfig ι, ⟪wightmanBasis WData A, Φ⟫_ℂ = 0) :
    Φ = 0 := by
  have h_pre : ∀ Ψ : WightmanPreHilbertSpace WData,
      ⟪toWightmanHilbert WData Ψ, Φ⟫_ℂ = 0 := by
    intro Ψ
    have h_expand : toWightmanHilbert WData Ψ =
        ∑ A ∈ Ψ.toFinsupp.support,
          Ψ.toFinsupp A • wightmanBasis WData A := by
      conv_lhs => rw [wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData Ψ]
      rw [map_finsuppSum]
      unfold Finsupp.sum
      refine Finset.sum_congr rfl (fun A _ => (toWightmanHilbert WData).map_smul _ _)
    rw [h_expand, sum_inner]
    refine Finset.sum_eq_zero (fun A _ => ?_)
    rw [inner_smul_left, horth A, mul_zero]
  have h_all : ∀ x : WightmanHilbert WData, ⟪x, Φ⟫_ℂ = 0 := by
    intro x
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih Ψ => exact h_pre Ψ
  exact inner_self_eq_zero.mp (h_all Φ)

theorem eq_of_inner_wightmanBasis_eq
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    {Φ₁ Φ₂ : WightmanHilbert WData}
    (h : ∀ A : WightmanConfig ι,
      ⟪wightmanBasis WData A, Φ₁⟫_ℂ = ⟪wightmanBasis WData A, Φ₂⟫_ℂ) :
    Φ₁ = Φ₂ := by
  rw [← sub_eq_zero]
  refine eq_zero_of_inner_wightmanBasis_eq_zero WData (fun A => ?_)
  rw [inner_sub_right, h A, sub_self]

theorem phase4_wightman_field_cyclicity_master
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (q : Fin 4 → ℝ) :
    WightmanVacuumCyclic WData ∧
    (∀ (Φ : WightmanHilbert WData),
      (∀ A : WightmanConfig ι, ⟪wightmanBasis WData A, Φ⟫_ℂ = 0) → Φ = 0) ∧
    (∀ (a : Fin 4 → ℝ) (A : WightmanConfig ι)
      (Ψ : WightmanPreHilbertSpace WData),
      wightmanTranslateLM WData a (wightmanFieldLM WData A Ψ) =
        wightmanFieldLM WData (wightmanConfigTranslate a A)
          (wightmanTranslateLM WData a Ψ)) ∧
    (∀ (L : SL2C) (A : WightmanConfig ι)
      (Ψ : WightmanPreHilbertSpace WData),
      wightmanScalarLorentzLM WData L (wightmanFieldLM WData A Ψ) =
        wightmanFieldLM WData (wightmanConfigLorentz L A)
          (wightmanScalarLorentzLM WData L Ψ)) ∧
    (∀ (n : ℕ) (α : Fin n → Unit) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
      ⟪wightmanVacuum (fourMomentumWightmanData q),
        fourMomentumSchwartzVec q n f⟫_ℂ =
      fourMomentumW q n α f) ∧
    (∀ (a : Fin 4 → ℝ) (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
      wightmanTranslate (fourMomentumWightmanData q)
        (fourMomentumW_wightmanTranslationInvariant q) a
        (fourMomentumSchwartzVec q n f) =
      fourMomentumSchwartzVec q n (schwartzDiagTranslateN n a f)) :=
  ⟨wightmanVacuumCyclic WData,
   fun _ => eq_zero_of_inner_wightmanBasis_eq_zero WData,
   wightmanTranslateLM_wightmanFieldLM WData,
   wightmanScalarLorentzLM_wightmanFieldLM WData,
   inner_wightmanVacuum_fourMomentumSchwartzVec q,
   fun a n f => wightmanTranslate_fourMomentumSchwartzVec q a n f⟩

omit [Fintype ι] [DecidableEq ι] in
theorem minkowskiInner_nonneg_of_mem_closure_forward_light_cone
    {q v : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone)
    (hv : v ∈ forward_light_cone) :
    0 ≤ minkowskiInner q v := by
  have h_bound := minkowskiInner_ge_coneGap_closure v q hq
  have h_gap := coneGap_pos v hv
  have hq0 : 0 ≤ q 0 := (closure_forward_light_cone_subset hq).1
  have h_prod : 0 ≤ coneGap v * q 0 := mul_nonneg (le_of_lt h_gap) hq0
  exact h_prod.trans h_bound

omit [Fintype ι] [DecidableEq ι] in
noncomputable def wightmanComplexTranslatePhase
    (q a v : Fin 4 → ℝ) : ℂ :=
  Complex.exp
    (Complex.I * ((minkowskiInner q a : ℝ) : ℂ) -
      ((minkowskiInner q v : ℝ) : ℂ))

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma norm_wightmanComplexTranslatePhase (q a v : Fin 4 → ℝ) :
    ‖wightmanComplexTranslatePhase q a v‖ =
      Real.exp (-minkowskiInner q v) := by
  unfold wightmanComplexTranslatePhase
  rw [Complex.norm_exp]
  congr 1
  simp

omit [Fintype ι] [DecidableEq ι] in
theorem norm_wightmanComplexTranslatePhase_le_one_iff
    (q a v : Fin 4 → ℝ) :
    ‖wightmanComplexTranslatePhase q a v‖ ≤ 1 ↔
      0 ≤ minkowskiInner q v := by
  rw [norm_wightmanComplexTranslatePhase, Real.exp_le_one_iff]
  constructor <;> intro h <;> linarith

omit [Fintype ι] [DecidableEq ι] in
theorem norm_wightmanComplexTranslatePhase_le_one_of_mem_closure_forward_light_cone
    {q : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone)
    (a : Fin 4 → ℝ) {v : Fin 4 → ℝ} (hv : v ∈ forward_light_cone) :
    ‖wightmanComplexTranslatePhase q a v‖ ≤ 1 := by
  rw [norm_wightmanComplexTranslatePhase_le_one_iff]
  exact minkowskiInner_nonneg_of_mem_closure_forward_light_cone hq hv

def WightmanEigenstatePositiveEnergy
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) : Prop :=
  ∀ (p : Fin 4 → ℝ) (Ψ : WightmanHilbert WData),
    Ψ ≠ 0 →
    (∀ a : Fin 4 → ℝ,
      wightmanTranslate WData htrans a Ψ =
        Complex.exp (Complex.I * ((minkowskiInner p a : ℝ) : ℂ)) • Ψ) →
    ∀ v ∈ forward_light_cone, 0 ≤ minkowskiInner p v

theorem wightmanEigenstate_timeEnergy_nonneg
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (hposE : WightmanEigenstatePositiveEnergy WData htrans)
    {p : Fin 4 → ℝ} {Ψ : WightmanHilbert WData} (hΨ : Ψ ≠ 0)
    (heig : ∀ a : Fin 4 → ℝ,
      wightmanTranslate WData htrans a Ψ =
        Complex.exp (Complex.I * ((minkowskiInner p a : ℝ) : ℂ)) • Ψ) :
    0 ≤ p 0 := by
  have h1 := hposE p Ψ hΨ heig (euclidTimeVec 1)
    timeUnitVec_mem_forward_light_cone
  have h_inner : minkowskiInner p (euclidTimeVec 1) = p 0 := by
    simp [minkowskiInner_explicit, euclidTimeVec]
  rwa [h_inner] at h1

theorem wightmanEigenstate_eq_zero_of_zeroMomentumSpectrumCondition
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hspec : ZeroMomentumSpectrumCondition WData.W)
    (htrans : WightmanTranslationInvariant WData.W)
    {p : Fin 4 → ℝ} {Ψ : WightmanHilbert WData} (hΨ : Ψ ≠ 0)
    (heig : ∀ a : Fin 4 → ℝ,
      wightmanTranslate WData htrans a Ψ =
        Complex.exp (Complex.I * ((minkowskiInner p a : ℝ) : ℂ)) • Ψ) :
    p = 0 := by
  by_contra hp
  obtain ⟨a, ha⟩ := exists_minkowskiInner_eq_pi_of_ne_zero hp
  have h1 := heig a
  rw [wightmanTranslate_eq_id_of_zeroMomentumSpectrumCondition
      WData hspec htrans a,
      ContinuousLinearMap.id_apply, ha] at h1
  have h_sub :
      (Complex.exp (Complex.I * (Real.pi : ℂ)) - 1) • Ψ = 0 := by
    rw [sub_smul, one_smul, ← h1, sub_self]
  exact hΨ ((smul_eq_zero.mp h_sub).resolve_left exp_I_mul_pi_sub_one_ne_zero)

theorem wightmanEigenstatePositiveEnergy_of_zeroMomentumSpectrumCondition
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hspec : ZeroMomentumSpectrumCondition WData.W)
    (htrans : WightmanTranslationInvariant WData.W) :
    WightmanEigenstatePositiveEnergy WData htrans := by
  intro p Ψ hΨ heig v _hv
  have hp0 :=
    wightmanEigenstate_eq_zero_of_zeroMomentumSpectrumCondition
      WData hspec htrans hΨ heig
  subst hp0
  simp [minkowskiInner_explicit]

theorem fourMomentumWightman_eigenstate_momentum_eq_zero_or_eq
    (q p : Fin 4 → ℝ) {Ψ : WightmanHilbert (fourMomentumWightmanData q)}
    (hΨ : Ψ ≠ 0)
    (heig : ∀ a : Fin 4 → ℝ,
      wightmanTranslate (fourMomentumWightmanData q)
        (fourMomentumW_wightmanTranslationInvariant q) a Ψ =
      Complex.exp (Complex.I * ((minkowskiInner p a : ℝ) : ℂ)) • Ψ) :
    p = 0 ∨ p = q := by
  by_cases hc0 : ⟪wightmanVacuum (fourMomentumWightmanData q), Ψ⟫_ℂ = 0
  · have hc1 : ⟪fourMomentumWightmanOneParticle q, Ψ⟫_ℂ ≠ 0 := by
      intro hc1_zero
      apply hΨ
      rw [fourMomentumWightmanHilbert_eq_vacuum_add_oneParticle q Ψ,
          hc0, hc1_zero, zero_smul, zero_smul, add_zero]
    refine Or.inr ?_
    by_contra hpq
    have h_sub_ne : p - q ≠ 0 := sub_ne_zero.mpr hpq
    obtain ⟨a, ha⟩ := exists_minkowskiInner_eq_pi_of_ne_zero h_sub_ne
    have h_act :
        ⟪fourMomentumWightmanOneParticle q,
          wightmanTranslate (fourMomentumWightmanData q)
            (fourMomentumW_wightmanTranslationInvariant q) a Ψ⟫_ℂ =
        ⟪fourMomentumWightmanOneParticle q,
          Complex.exp (Complex.I * ((minkowskiInner p a : ℝ) : ℂ)) • Ψ⟫_ℂ :=
      congrArg (fun x => ⟪fourMomentumWightmanOneParticle q, x⟫_ℂ) (heig a)
    rw [wightmanTranslate_fourMomentumWightmanData_apply,
        inner_add_right, inner_smul_right, inner_smul_right,
        inner_smul_right,
        inner_fourMomentumWightmanOneParticle_wightmanVacuum,
        inner_fourMomentumWightmanOneParticle_self,
        mul_zero, mul_one, zero_add] at h_act
    have h_exp_q_ne :
        Complex.exp (Complex.I * ((minkowskiInner q a : ℝ) : ℂ)) ≠ 0 :=
      Complex.exp_ne_zero _
    have h_diff_inner :
        minkowskiInner p a = Real.pi + minkowskiInner q a := by
      have h_sub_inner :
          minkowskiInner (p - q) a =
            minkowskiInner p a - minkowskiInner q a := by
        simp [minkowskiInner_explicit]
        ring
      linarith
    have h_exp_p :
        Complex.exp (Complex.I * ((minkowskiInner p a : ℝ) : ℂ)) =
        Complex.exp (Complex.I * (Real.pi : ℂ)) *
          Complex.exp (Complex.I * ((minkowskiInner q a : ℝ) : ℂ)) := by
      rw [h_diff_inner, Complex.ofReal_add, mul_add, Complex.exp_add]
    rw [h_exp_p, inner_smul_right] at h_act
    have h_zero :
        (Complex.exp (Complex.I * (Real.pi : ℂ)) - 1) *
          (Complex.exp (Complex.I * ((minkowskiInner q a : ℝ) : ℂ)) *
            ⟪fourMomentumWightmanOneParticle q, Ψ⟫_ℂ) = 0 := by
      linear_combination -h_act
    have h_prod_ne :
        Complex.exp (Complex.I * ((minkowskiInner q a : ℝ) : ℂ)) *
          ⟪fourMomentumWightmanOneParticle q, Ψ⟫_ℂ ≠ 0 :=
      mul_ne_zero h_exp_q_ne hc1
    exact h_prod_ne
      ((mul_eq_zero.mp h_zero).resolve_left exp_I_mul_pi_sub_one_ne_zero)
  · refine Or.inl ?_
    by_contra hp
    obtain ⟨a, ha⟩ := exists_minkowskiInner_eq_pi_of_ne_zero hp
    have h_act :
        ⟪wightmanVacuum (fourMomentumWightmanData q),
          wightmanTranslate (fourMomentumWightmanData q)
            (fourMomentumW_wightmanTranslationInvariant q) a Ψ⟫_ℂ =
        ⟪wightmanVacuum (fourMomentumWightmanData q),
          Complex.exp (Complex.I * ((minkowskiInner p a : ℝ) : ℂ)) • Ψ⟫_ℂ :=
      congrArg
        (fun x => ⟪wightmanVacuum (fourMomentumWightmanData q), x⟫_ℂ) (heig a)
    rw [wightmanTranslate_fourMomentumWightmanData_apply,
        inner_add_right, inner_smul_right, inner_smul_right,
        inner_smul_right,
        inner_wightmanVacuum_fourMomentumWightmanData_self,
        inner_wightmanVacuum_fourMomentumWightmanOneParticle,
        mul_one, mul_zero, mul_zero, add_zero, ha,
        inner_smul_right] at h_act
    have h_zero :
        (Complex.exp (Complex.I * (Real.pi : ℂ)) - 1) *
          ⟪wightmanVacuum (fourMomentumWightmanData q), Ψ⟫_ℂ = 0 := by
      linear_combination -h_act
    exact hc0
      ((mul_eq_zero.mp h_zero).resolve_left exp_I_mul_pi_sub_one_ne_zero)

theorem wightmanEigenstatePositiveEnergy_fourMomentumWightmanData_iff
    (q : Fin 4 → ℝ) :
    WightmanEigenstatePositiveEnergy (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) ↔
      ∀ v ∈ forward_light_cone, 0 ≤ minkowskiInner q v := by
  refine ⟨fun hpos v hv => ?_, fun hq p Ψ hΨ heig v hv => ?_⟩
  · exact hpos q (fourMomentumWightmanOneParticle q)
      (fourMomentumWightmanOneParticle_ne_zero q)
      (wightmanTranslate_fourMomentumWightmanOneParticle q) v hv
  · rcases fourMomentumWightman_eigenstate_momentum_eq_zero_or_eq
      q p hΨ heig with rfl | rfl
    · simp [minkowskiInner_explicit]
    · exact hq v hv

theorem wightmanEigenstatePositiveEnergy_fourMomentumWightmanData_of_mem_closure
    {q : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone) :
    WightmanEigenstatePositiveEnergy (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) := by
  rw [wightmanEigenstatePositiveEnergy_fourMomentumWightmanData_iff]
  intro v hv
  exact minkowskiInner_nonneg_of_mem_closure_forward_light_cone hq hv

structure WightmanAxioms (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (η : ℂ) where
  WData : WightmanPositiveData R S
  E : TubeExtension WData.W
  positivity : Positivity S WData.W
  poincare : PoincareCovariant R WData.W
  spectrum : ForwardConeSpectrumCondition WData.W
  weakLocality : WeakLocality η WData.W
  tube_covariant : TubeCovariant R E
  tube_pct : TubePCT η R E
  cyclic : WightmanVacuumCyclic WData

namespace WightmanAxioms

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ}

abbrev Hilbert (A : WightmanAxioms R S η) : Type _ :=
  WightmanHilbert A.WData

noncomputable def vacuum (A : WightmanAxioms R S η) : A.Hilbert :=
  wightmanVacuum A.WData

noncomputable def basis (A : WightmanAxioms R S η)
    (cfg : WightmanConfig ι) : A.Hilbert :=
  wightmanBasis A.WData cfg

theorem translationInvariant (A : WightmanAxioms R S η) :
    WightmanTranslationInvariant A.WData.W :=
  wightmanTranslationInvariant_of_poincare R A.poincare

noncomputable def translate (A : WightmanAxioms R S η) (a : Fin 4 → ℝ) :
    A.Hilbert →L[ℂ] A.Hilbert :=
  wightmanTranslate A.WData A.translationInvariant a

noncomputable def spatialTranslate (A : WightmanAxioms R S η)
    (a : Fin 3 → ℝ) : A.Hilbert →L[ℂ] A.Hilbert :=
  wightmanSpatialTranslate A.WData A.translationInvariant a

noncomputable def timeTranslate (A : WightmanAxioms R S η) (t : ℝ) :
    A.Hilbert →L[ℂ] A.Hilbert :=
  wightmanTimeTranslate A.WData A.translationInvariant t

@[simp]
theorem translate_zero (A : WightmanAxioms R S η) :
    A.translate 0 = ContinuousLinearMap.id ℂ A.Hilbert :=
  wightmanTranslate_zero A.WData A.translationInvariant

theorem translate_add (A : WightmanAxioms R S η) (a b : Fin 4 → ℝ) :
    A.translate (a + b) = (A.translate a).comp (A.translate b) :=
  wightmanTranslate_add A.WData A.translationInvariant a b

@[simp]
theorem translate_vacuum (A : WightmanAxioms R S η) (a : Fin 4 → ℝ) :
    A.translate a A.vacuum = A.vacuum :=
  wightmanTranslate_vacuum A.WData A.translationInvariant a

theorem inner_translate (A : WightmanAxioms R S η) (a : Fin 4 → ℝ)
    (x y : A.Hilbert) :
    ⟪A.translate a x, A.translate a y⟫_ℂ = ⟪x, y⟫_ℂ :=
  inner_wightmanTranslate A.WData A.translationInvariant a x y

theorem norm_translate (A : WightmanAxioms R S η) (a : Fin 4 → ℝ)
    (x : A.Hilbert) :
    ‖A.translate a x‖ = ‖x‖ :=
  norm_wightmanTranslate A.WData A.translationInvariant a x

theorem complexCovariant (A : WightmanAxioms R S η) :
    ComplexCovariant R A.E :=
  complex_covariance_of_real R A.WData.W A.E A.tube_covariant

noncomputable def H_ext (A : WightmanAxioms R S η) :
    ∀ n : ℕ, (Fin n → ι) → (Fin n → Fin 4 → ℂ) → ℂ :=
  spinor_H_ext R A.WData.W A.E

theorem H_ext_analytic (A : WightmanAxioms R S η) (n : ℕ) (α : Fin n → ι) :
    AnalyticOn ℂ (A.H_ext n α) (extended_tube_n n) :=
  spinor_H_ext_analytic R A.WData.W A.E A.tube_covariant n α

theorem extendedTubeWeakLocality (A : WightmanAxioms R S η) :
    ExtendedTubeWeakLocality η A.H_ext :=
  extendedTubeWeakLocality_of_weakLocality R A.WData.W A.E
    A.tube_covariant A.weakLocality

theorem wightman_pct (A : WightmanAxioms R S η) :
    WightmanPCT η R A.WData.W :=
  wightman_pct_of_spectrumCondition R A.WData.W A.spectrum A.poincare A.weakLocality

theorem spin_statistics (A : WightmanAxioms R S η)
    {ε : ℂ} (hε : R.HasSpinParity ε)
    (h_exch : DistributionalTwoPointSpinExchange ε A.WData.W)
    (h_nondeg : ∃ β : Fin 2 → ι, A.WData.W 2 β ≠ 0) :
    η = ε :=
  spin_statistics_of_spectrumCondition R A.WData.W A.spectrum A.poincare hε
    A.weakLocality h_exch h_nondeg

theorem eq_zero_of_inner_basis_eq_zero (A : WightmanAxioms R S η)
    {Φ : A.Hilbert} (horth : ∀ cfg : WightmanConfig ι, ⟪A.basis cfg, Φ⟫_ℂ = 0) :
    Φ = 0 :=
  eq_zero_of_inner_wightmanBasis_eq_zero A.WData horth

end WightmanAxioms

structure WightmanAxiomsWithUniqueVacuum
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) extends
    WightmanAxioms R S η where
  vacuumNormalized : WightmanVacuumNormalized S WData.W
  cluster : ∀ a : Fin 4 → ℝ, a ≠ 0 → WightmanClusterAlong WData a
  vacuumUnique :
    WightmanVacuumUnique WData
      (wightmanTranslationInvariant_of_poincare R poincare)

namespace WightmanAxiomsWithUniqueVacuum

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ}

@[simp]
theorem inner_vacuum_self (A : WightmanAxiomsWithUniqueVacuum R S η) :
    ⟪A.toWightmanAxioms.vacuum, A.toWightmanAxioms.vacuum⟫_ℂ = 1 :=
  inner_wightmanVacuum_self_of_normalized A.WData A.vacuumNormalized

@[simp]
theorem norm_vacuum (A : WightmanAxiomsWithUniqueVacuum R S η) :
    ‖A.toWightmanAxioms.vacuum‖ = 1 :=
  norm_wightmanVacuum_of_normalized A.WData A.vacuumNormalized

theorem eq_smul_vacuum_of_translate_fixed
    (A : WightmanAxiomsWithUniqueVacuum R S η)
    {Ψ : A.toWightmanAxioms.Hilbert}
    (hfixed : ∀ a : Fin 4 → ℝ, A.toWightmanAxioms.translate a Ψ = Ψ) :
    Ψ = ⟪A.toWightmanAxioms.vacuum, Ψ⟫_ℂ • A.toWightmanAxioms.vacuum :=
  A.vacuumUnique Ψ hfixed

end WightmanAxiomsWithUniqueVacuum

namespace ForwardConeOSEuclideanTubeBridge

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

noncomputable def toWightmanAxioms
    (B : ForwardConeOSEuclideanTubeBridge R S η 𝒮) :
    WightmanAxioms R S η where
  WData := B.toWightmanPositiveData
  E := B.E
  positivity := B.positivity
  poincare := B.poincare
  spectrum := B.spectrum
  weakLocality := B.weakLocality
  tube_covariant := B.tube_covariant
  tube_pct := B.tube_pct
  cyclic := wightmanVacuumCyclic B.toWightmanPositiveData

end ForwardConeOSEuclideanTubeBridge

namespace OSEuclideanTubeBridge

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

noncomputable def toWightmanAxioms (B : OSEuclideanTubeBridge R S η 𝒮) :
    WightmanAxioms R S η :=
  B.toForwardConeOSEuclideanTubeBridge.toWightmanAxioms

end OSEuclideanTubeBridge

namespace ForwardConeOSReconstructedWightman

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

noncomputable def toWightmanAxioms
    (P : ForwardConeOSReconstructedWightman R S η 𝒮) :
    WightmanAxioms R S η where
  WData := P.toWightmanPositiveData
  E := P.E
  positivity := P.positivity
  poincare := P.poincare
  spectrum := P.spectrum
  weakLocality := P.weakLocality
  tube_covariant := P.tube_covariant
  tube_pct := P.tube_pct
  cyclic := wightmanVacuumCyclic P.toWightmanPositiveData

end ForwardConeOSReconstructedWightman

namespace OSReconstructionData

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}
  {hOS : OSAxioms R S η 𝒮}
  {hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData}

noncomputable def toWightmanAxioms
    (G : OSReconstructionData hOS hcluster) :
    WightmanAxioms R S η :=
  G.toForwardConeOSReconstructedWightman.toWightmanAxioms

@[simp]
theorem toWightmanAxioms_W
    (G : OSReconstructionData hOS hcluster) :
    G.toWightmanAxioms.WData.W = G.F.toWightmanFamily := rfl

@[simp]
theorem toWightmanAxioms_E
    (G : OSReconstructionData hOS hcluster) :
    G.toWightmanAxioms.E = G.F.toTubeExtension := rfl

end OSReconstructionData

namespace OSReconstructedWightman

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

noncomputable def toWightmanAxioms
    (P : OSReconstructedWightman R S η 𝒮) :
    WightmanAxioms R S η :=
  P.toForwardConeOSReconstructedWightman.toWightmanAxioms

noncomputable def toWightmanAxiomsWithUniqueVacuum
    (P : OSReconstructedWightman R S η 𝒮)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = vladimirovSchwinger P.W n α x)
    (hnorm : OSVacuumNormalized 𝒮)
    (hcluster : OSTimeClusterDecomposition P.osData) :
    WightmanAxiomsWithUniqueVacuum R S η where
  toWightmanAxioms := P.toWightmanAxioms
  vacuumNormalized :=
    (wightmanVacuumNormalized_iff_osVacuumNormalized_of_vladimirov
      P.osData P.W P.spectrum h_schw).mpr hnorm
  cluster a _ha :=
    (P.wightmanClusterAlong_iff_osTimeCluster h_schw a).mpr hcluster
  vacuumUnique :=
    (P.wightmanVacuumUnique_iff_osVacuumUnique h_schw).mpr
      (osVacuumUnique_of_timeCluster P.osData P.contraction hcluster)

end OSReconstructedWightman

noncomputable def vacWightmanAxioms
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) :
    WightmanAxioms R S η :=
  (vacOSReconstructedWightman R S η).toWightmanAxioms

noncomputable def vacWightmanAxiomsWithUniqueVacuum
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) :
    WightmanAxiomsWithUniqueVacuum R S η :=
  (vacOSReconstructedWightman R S η).toWightmanAxiomsWithUniqueVacuum
    (fun n α x _ => by
      change vacS n α x = vladimirovSchwinger vacW n α x
      rw [vladimirovSchwinger_vacW])
    vacS_vacuumNormalized
    (vacOSTimeCluster R S)

noncomputable def z2FreeWightmanAxioms :
    WightmanAxioms trivialRep trivialStarStructure 1 :=
  z2FreeOSReconstructedWightman.toWightmanAxioms

noncomputable def coherentWightmanAxiomsWithUniqueVacuum (r : ℝ) :
    WightmanAxiomsWithUniqueVacuum trivialRep trivialStarStructure 1 :=
  (coherentOSReconstructedWightman r).toWightmanAxiomsWithUniqueVacuum
    (fun n α x _ => by
      change coherentS r n α x = vladimirovSchwinger (coherentW r) n α x
      rw [coherentS, coherentW, vladimirovSchwinger_momentW])
    (by
      unfold OSVacuumNormalized coherentS momentS
      simp [coherentCoeff_apply])
    (coherentOSTimeCluster r)

theorem phase5_wightman_axioms_reconstruction_master
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ)
    (q : Fin 4 → ℝ) :
    (WightmanEigenstatePositiveEnergy (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) ↔
      ∀ v ∈ forward_light_cone, 0 ≤ minkowskiInner q v) ∧
    (q ∈ closure forward_light_cone →
      WightmanEigenstatePositiveEnergy (fourMomentumWightmanData q)
        (fourMomentumW_wightmanTranslationInvariant q) ∧
      ForwardConeSpectrumCondition (fourMomentumW q)) ∧
    WightmanVacuumCyclic (vacWightmanAxioms R S η).WData ∧
    WightmanVacuumUnique (vacWightmanAxiomsWithUniqueVacuum R S η).WData
      (vacWightmanAxiomsWithUniqueVacuum R S η).toWightmanAxioms.translationInvariant ∧
    WightmanVacuumCyclic z2FreeWightmanAxioms.WData :=
  ⟨wightmanEigenstatePositiveEnergy_fourMomentumWightmanData_iff q,
   fun hq =>
     ⟨wightmanEigenstatePositiveEnergy_fourMomentumWightmanData_of_mem_closure hq,
      fourMomentumW_forwardConeSpectrumCondition hq⟩,
   (vacWightmanAxioms R S η).cyclic,
   (vacWightmanAxiomsWithUniqueVacuum R S η).vacuumUnique,
   z2FreeWightmanAxioms.cyclic⟩

theorem wightman_bridge_grand_master
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ)
    (W : WightmanFamily ι)
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    {q : Fin 4 → ℝ} (hq0 : 0 ≤ q 0) :
    ((CompactPositivity S W ↔
      (WightmanKernelPositive S W ∧ WightmanKernelHermiticity S W)) ∧
     (ZeroMomentumSpectrumCondition W →
      (Positivity S W ↔
        (WightmanKernelPositive S W ∧ WightmanKernelHermiticity S W)))) ∧
    ((∀ a b : Fin 4 → ℝ,
      wightmanTranslate WData htrans (a + b) =
        (wightmanTranslate WData htrans a).comp
          (wightmanTranslate WData htrans b)) ∧
     (∀ (t : ℝ) (Φ : OSHilbert (fourMomentumOSData q)),
      fourMomentumOSWightmanLinearIsometryEquiv q
        ((fourMomentumOSHolomorphicSemigroup hq0).realTimeUnitary (-t) Φ) =
      wightmanTimeTranslate (fourMomentumWightmanData q)
        (fourMomentumW_wightmanTranslationInvariant q) t
        (fourMomentumOSWightmanLinearIsometryEquiv q Φ))) ∧
    ((WightmanVacuumUnique (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) ↔ q ≠ 0) ∧
     (WightmanTimeVacuumUnique (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) ↔ q 0 ≠ 0)) ∧
    (WightmanVacuumCyclic WData ∧
     (∀ (a : Fin 4 → ℝ) (A : WightmanConfig ι)
       (Ψ : WightmanPreHilbertSpace WData),
       wightmanTranslateLM WData a (wightmanFieldLM WData A Ψ) =
         wightmanFieldLM WData (wightmanConfigTranslate a A)
           (wightmanTranslateLM WData a Ψ))) ∧
    ((WightmanEigenstatePositiveEnergy (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) ↔
      ∀ v ∈ forward_light_cone, 0 ≤ minkowskiInner q v) ∧
     WightmanVacuumUnique (vacWightmanAxiomsWithUniqueVacuum R S η).WData
       (vacWightmanAxiomsWithUniqueVacuum R S η).toWightmanAxioms.translationInvariant) :=
  ⟨⟨compactPositivity_iff_wightmanKernelPositive_and_hermiticity S W,
    positivity_iff_wightmanKernelPositive_and_hermiticity_of_zeroMomentumSpectrumCondition S⟩,
   ⟨wightmanTranslate_add WData htrans,
    fourMomentumOSWightmanLinearIsometryEquiv_intertwines_realTimeUnitary hq0⟩,
   ⟨wightmanVacuumUnique_fourMomentumWightmanData_iff q,
    wightmanTimeVacuumUnique_fourMomentumWightmanData_iff q⟩,
   ⟨wightmanVacuumCyclic WData,
    wightmanTranslateLM_wightmanFieldLM WData⟩,
   ⟨wightmanEigenstatePositiveEnergy_fourMomentumWightmanData_iff q,
    (vacWightmanAxiomsWithUniqueVacuum R S η).vacuumUnique⟩⟩

def compactCutoff (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (m : ℕ) :
    CompactSchwartz n :=
  ⟨schwartzCutoffSeq n f m, schwartzCutoffSeq_hasCompactSupport n f m⟩

@[simp]
lemma compactCutoff_val (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (m : ℕ) :
    (compactCutoff n f m).val = schwartzCutoffSeq n f m := rfl

def concatProjLeftCLM (j k : ℕ) :
    (Fin (j + k) → Fin 4 → ℝ) →L[ℝ] (Fin j → Fin 4 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x i => x (Fin.castAdd k (Fin.rev i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

def concatProjRightCLM (j k : ℕ) :
    (Fin (j + k) → Fin 4 → ℝ) →L[ℝ] (Fin k → Fin 4 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x i => x (Fin.natAdd j i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp]
lemma concatProjLeftCLM_apply (j k : ℕ) (x : Fin (j + k) → Fin 4 → ℝ) (i : Fin j) :
    concatProjLeftCLM j k x i = x (Fin.castAdd k (Fin.rev i)) := rfl

@[simp]
lemma concatProjRightCLM_apply (j k : ℕ) (x : Fin (j + k) → Fin 4 → ℝ) (i : Fin k) :
    concatProjRightCLM j k x i = x (Fin.natAdd j i) := rfl

lemma norm_concatProjLeftCLM_apply_le (j k : ℕ) (x : Fin (j + k) → Fin 4 → ℝ) :
    ‖concatProjLeftCLM j k x‖ ≤ ‖x‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr (fun i =>
    norm_le_pi_norm x (Fin.castAdd k (Fin.rev i)))

lemma norm_concatProjRightCLM_apply_le (j k : ℕ) (x : Fin (j + k) → Fin 4 → ℝ) :
    ‖concatProjRightCLM j k x‖ ≤ ‖x‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr (fun i =>
    norm_le_pi_norm x (Fin.natAdd j i))

lemma opNorm_concatProjLeftCLM_le_one (j k : ℕ) :
    ‖concatProjLeftCLM j k‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    simpa [one_mul] using norm_concatProjLeftCLM_apply_le j k x)

lemma opNorm_concatProjRightCLM_le_one (j k : ℕ) :
    ‖concatProjRightCLM j k‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    simpa [one_mul] using norm_concatProjRightCLM_apply_le j k x)

lemma starRingEnd_vladimirov_cutoff_bump_schwartz (n : ℕ) (y : Fin n → Fin 4 → ℝ) :
    (starRingEnd ℂ) (vladimirov_cutoff_bump_schwartz n y) =
      vladimirov_cutoff_bump_schwartz n y := by
  change (starRingEnd ℂ) ((vladimirovCutoffBump n 1 Real.zero_lt_one y : ℝ) : ℂ) =
    ((vladimirovCutoffBump n 1 Real.zero_lt_one y : ℝ) : ℂ)
  exact Complex.conj_ofReal _

lemma norm_iteratedFDeriv_bump_comp_clm_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (n : ℕ)
    (L : E →L[ℝ] (Fin n → Fin 4 → ℝ)) (hL : ‖L‖ ≤ 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (q : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ q
      (fun y : E => vladimirov_cutoff_bump_schwartz n (r • L y)) x‖ ≤
      SchwartzMap.seminorm ℝ 0 q (vladimirov_cutoff_bump_schwartz n) := by
  let M : E →L[ℝ] (Fin n → Fin 4 → ℝ) := r • L
  have hM_norm : ‖M‖ ≤ 1 := by
    dsimp [M]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0]
    nlinarith [norm_nonneg L]
  have h_smooth : ContDiff ℝ (q : ℕ∞)
      (vladimirov_cutoff_bump_schwartz n : (Fin n → Fin 4 → ℝ) → ℂ) :=
    ((vladimirov_cutoff_bump_schwartz n).smooth ⊤).of_le (WithTop.coe_le_coe.mpr le_top)
  have h_fn : (fun y : E => vladimirov_cutoff_bump_schwartz n (r • L y)) =
      (vladimirov_cutoff_bump_schwartz n : (Fin n → Fin 4 → ℝ) → ℂ) ∘ M := rfl
  rw [h_fn, M.iteratedFDeriv_comp_right h_smooth x (le_refl _)]
  have h_comp := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ q (vladimirov_cutoff_bump_schwartz n : (Fin n → Fin 4 → ℝ) → ℂ) (M x))
    (fun _ : Fin q => M)
  have h_prod : (∏ _ : Fin q, ‖M‖) ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg M) (fun _ _ => hM_norm)
  have h_sem := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ
    (vladimirov_cutoff_bump_schwartz n) q (M x)
  calc ‖(iteratedFDeriv ℝ q (vladimirov_cutoff_bump_schwartz n) (M x)).compContinuousLinearMap
        (fun _ => M)‖
      ≤ ‖iteratedFDeriv ℝ q (vladimirov_cutoff_bump_schwartz n) (M x)‖ *
          ∏ _ : Fin q, ‖M‖ := h_comp
    _ ≤ SchwartzMap.seminorm ℝ 0 q (vladimirov_cutoff_bump_schwartz n) * 1 :=
        mul_le_mul h_sem h_prod (Finset.prod_nonneg (fun _ _ => norm_nonneg M))
          (apply_nonneg _ _)
    _ = SchwartzMap.seminorm ℝ 0 q (vladimirov_cutoff_bump_schwartz n) := mul_one _

lemma norm_iteratedFDeriv_concatBumpDiff_le (j k m i : ℕ)
    (x : Fin (j + k) → Fin 4 → ℝ) :
    ‖iteratedFDeriv ℝ i
      (fun y : Fin (j + k) → Fin 4 → ℝ =>
        vladimirov_cutoff_bump_schwartz j
          ((((m : ℝ) + 1)⁻¹) • concatProjLeftCLM j k y) *
        vladimirov_cutoff_bump_schwartz k
          ((((m : ℝ) + 1)⁻¹) • concatProjRightCLM j k y) - 1) x‖ ≤
      (∑ q ∈ Finset.range (i + 1),
        (i.choose q : ℝ) *
          SchwartzMap.seminorm ℝ 0 q (vladimirov_cutoff_bump_schwartz j) *
          SchwartzMap.seminorm ℝ 0 (i - q) (vladimirov_cutoff_bump_schwartz k)) + 1 := by
  let r : ℝ := ((m : ℝ) + 1)⁻¹
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) m])
  let b₁ : (Fin (j + k) → Fin 4 → ℝ) → ℂ :=
    fun y => vladimirov_cutoff_bump_schwartz j (r • concatProjLeftCLM j k y)
  let b₂ : (Fin (j + k) → Fin 4 → ℝ) → ℂ :=
    fun y => vladimirov_cutoff_bump_schwartz k (r • concatProjRightCLM j k y)
  have hb₁_smooth : ContDiff ℝ (⊤ : ℕ∞) b₁ :=
    ((vladimirov_cutoff_bump_schwartz j).smooth ⊤).comp
      ((r • concatProjLeftCLM j k).contDiff)
  have hb₂_smooth : ContDiff ℝ (⊤ : ℕ∞) b₂ :=
    ((vladimirov_cutoff_bump_schwartz k).smooth ⊤).comp
      ((r • concatProjRightCLM j k).contDiff)
  cases i with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    have h1 := norm_iteratedFDeriv_bump_comp_clm_le j (concatProjLeftCLM j k)
      (opNorm_concatProjLeftCLM_le_one j k) hr0 hr1 0 x
    have h2 := norm_iteratedFDeriv_bump_comp_clm_le k (concatProjRightCLM j k)
      (opNorm_concatProjRightCLM_le_one j k) hr0 hr1 0 x
    rw [norm_iteratedFDeriv_zero] at h1 h2
    have h_mul : ‖b₁ x * b₂ x‖ ≤
        SchwartzMap.seminorm ℝ 0 0 (vladimirov_cutoff_bump_schwartz j) *
          SchwartzMap.seminorm ℝ 0 0 (vladimirov_cutoff_bump_schwartz k) := by
      rw [norm_mul]
      exact mul_le_mul h1 h2 (norm_nonneg _) (apply_nonneg _ _)
    calc ‖b₁ x * b₂ x - 1‖
        ≤ ‖b₁ x * b₂ x‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖b₁ x * b₂ x‖ + 1 := by simp
      _ ≤ (∑ q ∈ Finset.range 1,
            ((0 : ℕ).choose q : ℝ) *
              SchwartzMap.seminorm ℝ 0 q (vladimirov_cutoff_bump_schwartz j) *
              SchwartzMap.seminorm ℝ 0 (0 - q) (vladimirov_cutoff_bump_schwartz k)) + 1 := by
          simp only [Finset.range_one, Finset.sum_singleton, Nat.choose_self,
            Nat.cast_one, one_mul, Nat.sub_self]
          linarith
  | succ p =>
    have h_prod_smooth : ContDiff ℝ (p + 1 : ℕ) (fun y => b₁ y * b₂ y) :=
      (hb₁_smooth.mul hb₂_smooth).of_le (WithTop.coe_le_coe.mpr le_top)
    have h_const_smooth : ContDiff ℝ (p + 1 : ℕ)
        (fun _ : Fin (j + k) → Fin 4 → ℝ => (1 : ℂ)) := contDiff_const
    change ‖iteratedFDeriv ℝ (p + 1)
      ((fun y => b₁ y * b₂ y) - fun _ => (1 : ℂ)) x‖ ≤ _
    rw [iteratedFDeriv_sub_apply h_prod_smooth.contDiffAt h_const_smooth.contDiffAt,
        iteratedFDeriv_const_of_ne (Nat.succ_ne_zero p) (1 : ℂ), Pi.zero_apply, sub_zero]
    have h_leib := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := b₁) (g := b₂)
      (n := p + 1) (N := (⊤ : ℕ∞)) hb₁_smooth hb₂_smooth x (WithTop.coe_le_coe.mpr le_top)
    have h_sum_le :
        (∑ q ∈ Finset.range (p + 1 + 1),
          ((p + 1).choose q : ℝ) * ‖iteratedFDeriv ℝ q b₁ x‖ *
            ‖iteratedFDeriv ℝ (p + 1 - q) b₂ x‖) ≤
        ∑ q ∈ Finset.range (p + 1 + 1),
          ((p + 1).choose q : ℝ) *
            SchwartzMap.seminorm ℝ 0 q (vladimirov_cutoff_bump_schwartz j) *
            SchwartzMap.seminorm ℝ 0 (p + 1 - q) (vladimirov_cutoff_bump_schwartz k) := by
      refine Finset.sum_le_sum (fun q _ => ?_)
      have hq1 := norm_iteratedFDeriv_bump_comp_clm_le j (concatProjLeftCLM j k)
        (opNorm_concatProjLeftCLM_le_one j k) hr0 hr1 q x
      have hq2 := norm_iteratedFDeriv_bump_comp_clm_le k (concatProjRightCLM j k)
        (opNorm_concatProjRightCLM_le_one j k) hr0 hr1 (p + 1 - q) x
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hq1 (Nat.cast_nonneg _))
        hq2 (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _))
    linarith

theorem tendsto_wightmanConcatSchwartz_compactCutoff (j k : ℕ)
    (f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (g : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ)
    (G : SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ)
    (hG : ∀ x : Fin (j + k) → Fin 4 → ℝ,
      G x = (starRingEnd ℂ) (f (fun i => x (Fin.castAdd k (Fin.rev i)))) *
        g (fun i => x (Fin.natAdd j i))) :
    Tendsto
      (fun m : ℕ =>
        wightmanConcatSchwartz j k (compactCutoff j f m) (compactCutoff k g m))
      Filter.atTop (𝓝 G) := by
  let H_seq : ℕ → SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ :=
    fun m => wightmanConcatSchwartz j k (compactCutoff j f m) (compactCutoff k g m)
  have h_sub : Tendsto (fun m => H_seq m - G) Filter.atTop (𝓝 0) := by
    rw [(schwartz_withSeminorms ℝ (Fin (j + k) → Fin 4 → ℝ) ℂ).tendsto_nhds _ 0]
    rintro ⟨l, n_der⟩ ε hε
    let K_bump : ℕ → ℝ := fun i =>
      (∑ q ∈ Finset.range (i + 1),
        (i.choose q : ℝ) *
          SchwartzMap.seminorm ℝ 0 q (vladimirov_cutoff_bump_schwartz j) *
          SchwartzMap.seminorm ℝ 0 (i - q) (vladimirov_cutoff_bump_schwartz k)) + 1
    let C : ℝ := ∑ i ∈ Finset.range (n_der + 1),
      (n_der.choose i : ℝ) * K_bump i * SchwartzMap.seminorm ℝ (l + 1) (n_der - i) G
    have hK_nonneg : ∀ i, 0 ≤ K_bump i := fun i =>
      add_nonneg (Finset.sum_nonneg (fun q _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _))
          (apply_nonneg _ _))) zero_le_one
    have hC_nonneg : 0 ≤ C :=
      Finset.sum_nonneg (fun i _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hK_nonneg i)) (apply_nonneg _ _))
    have h_bound_m : ∀ m : ℕ,
        SchwartzMap.seminorm ℝ l n_der (H_seq m - G) ≤ C * (((m : ℝ) + 1)⁻¹) := by
      intro m
      have hm_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      refine SchwartzMap.seminorm_le_bound ℝ l n_der (H_seq m - G)
        (mul_nonneg hC_nonneg (inv_nonneg.mpr hm_pos.le)) (fun x => ?_)
      let d : (Fin (j + k) → Fin 4 → ℝ) → ℂ := fun y =>
        vladimirov_cutoff_bump_schwartz j
          ((((m : ℝ) + 1)⁻¹) • concatProjLeftCLM j k y) *
        vladimirov_cutoff_bump_schwartz k
          ((((m : ℝ) + 1)⁻¹) • concatProjRightCLM j k y) - 1
      have h_fn_eq :
          ((H_seq m - G : SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ) :
            (Fin (j + k) → Fin 4 → ℝ) → ℂ) =
          fun y => d y * G y := by
        ext y
        change wightmanConcatSchwartz j k (compactCutoff j f m) (compactCutoff k g m) y - G y =
          d y * G y
        rw [wightmanConcatSchwartz_apply, compactCutoff_val, compactCutoff_val,
            schwartzCutoffSeq_apply, schwartzCutoffSeq_apply, map_mul,
            starRingEnd_vladimirov_cutoff_bump_schwartz, hG y]
        dsimp [d, concatProjLeftCLM, concatProjRightCLM]
        ring
      by_cases hx : ‖x‖ < (m : ℝ) + 1
      · have h_ev :
            ((H_seq m - G : SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ) :
              (Fin (j + k) → Fin 4 → ℝ) → ℂ) =ᶠ[𝓝 x]
              (fun _ => (0 : ℂ)) := by
          filter_upwards [Metric.isOpen_ball.mem_nhds
            (show x ∈ Metric.ball (0 : Fin (j + k) → Fin 4 → ℝ) ((m : ℝ) + 1) by
              simpa [Metric.mem_ball, dist_zero_right] using hx)] with y hy
          rw [Metric.mem_ball, dist_zero_right] at hy
          have hy_left :
              (((m : ℝ) + 1)⁻¹) • concatProjLeftCLM j k y ∈
                Metric.ball (0 : Fin j → Fin 4 → ℝ) 1 := by
            rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
                abs_of_pos (inv_pos.mpr hm_pos), inv_mul_lt_iff₀ hm_pos, mul_one]
            exact (norm_concatProjLeftCLM_apply_le j k y).trans_lt hy
          have hy_right :
              (((m : ℝ) + 1)⁻¹) • concatProjRightCLM j k y ∈
                Metric.ball (0 : Fin k → Fin 4 → ℝ) 1 := by
            rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
                abs_of_pos (inv_pos.mpr hm_pos), inv_mul_lt_iff₀ hm_pos, mul_one]
            exact (norm_concatProjRightCLM_apply_le j k y).trans_lt hy
          have h_one₁ :
              vladimirov_cutoff_bump_schwartz j
                ((((m : ℝ) + 1)⁻¹) • concatProjLeftCLM j k y) = 1 := by
            change ((vladimirovCutoffBump j 1 Real.zero_lt_one
              ((((m : ℝ) + 1)⁻¹) • concatProjLeftCLM j k y) : ℝ) : ℂ) = 1
            rw [vladimirov_cutoff_bump_one_of_mem_ball_gen j 1 le_rfl _ hy_left]
            simp
          have h_one₂ :
              vladimirov_cutoff_bump_schwartz k
                ((((m : ℝ) + 1)⁻¹) • concatProjRightCLM j k y) = 1 := by
            change ((vladimirovCutoffBump k 1 Real.zero_lt_one
              ((((m : ℝ) + 1)⁻¹) • concatProjRightCLM j k y) : ℝ) : ℂ) = 1
            rw [vladimirov_cutoff_bump_one_of_mem_ball_gen k 1 le_rfl _ hy_right]
            simp
          have h_pt := congrFun h_fn_eq y
          dsimp [d] at h_pt
          rw [h_one₁, h_one₂, one_mul, sub_self, zero_mul] at h_pt
          exact h_pt
        rw [(Filter.EventuallyEq.iteratedFDeriv ℝ h_ev n_der).eq_of_nhds,
            iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero]
        exact mul_nonneg hC_nonneg (inv_nonneg.mpr hm_pos.le)
      · push Not at hx
        have hd_smooth : ContDiff ℝ (⊤ : ℕ∞) d := by
          have hb₁ : ContDiff ℝ (⊤ : ℕ∞) (fun y =>
              vladimirov_cutoff_bump_schwartz j
                ((((m : ℝ) + 1)⁻¹) • concatProjLeftCLM j k y)) :=
            ((vladimirov_cutoff_bump_schwartz j).smooth ⊤).comp
              (((((m : ℝ) + 1)⁻¹) • concatProjLeftCLM j k).contDiff)
          have hb₂ : ContDiff ℝ (⊤ : ℕ∞) (fun y =>
              vladimirov_cutoff_bump_schwartz k
                ((((m : ℝ) + 1)⁻¹) • concatProjRightCLM j k y)) :=
            ((vladimirov_cutoff_bump_schwartz k).smooth ⊤).comp
              (((((m : ℝ) + 1)⁻¹) • concatProjRightCLM j k).contDiff)
          exact (hb₁.mul hb₂).sub contDiff_const
        rw [h_fn_eq]
        have h_leib := norm_iteratedFDeriv_mul_le (𝕜 := ℝ)
          (f := d) (g := (G : (Fin (j + k) → Fin 4 → ℝ) → ℂ))
          (n := n_der) (N := (⊤ : ℕ∞))
          hd_smooth (G.smooth ⊤) x (WithTop.coe_le_coe.mpr le_top)
        have h_norm_pow : ‖x‖ ^ l ≤ (((m : ℝ) + 1)⁻¹) * ‖x‖ ^ (l + 1) := by
          rw [le_inv_mul_iff₀ hm_pos]
          have h_mul : ((m : ℝ) + 1) * ‖x‖ ^ l ≤ ‖x‖ * ‖x‖ ^ l :=
            mul_le_mul_of_nonneg_right hx (pow_nonneg (norm_nonneg x) l)
          rwa [pow_succ']
        calc ‖x‖ ^ l * ‖iteratedFDeriv ℝ n_der (fun y => d y * G y) x‖
            ≤ ((((m : ℝ) + 1)⁻¹) * ‖x‖ ^ (l + 1)) *
                ∑ i ∈ Finset.range (n_der + 1),
                  (n_der.choose i : ℝ) * ‖iteratedFDeriv ℝ i d x‖ *
                    ‖iteratedFDeriv ℝ (n_der - i)
                      (G : (Fin (j + k) → Fin 4 → ℝ) → ℂ) x‖ :=
              mul_le_mul h_norm_pow h_leib (norm_nonneg _)
                (mul_nonneg (inv_nonneg.mpr hm_pos.le) (pow_nonneg (norm_nonneg x) (l + 1)))
          _ = (((m : ℝ) + 1)⁻¹) *
                ∑ i ∈ Finset.range (n_der + 1),
                  (n_der.choose i : ℝ) * ‖iteratedFDeriv ℝ i d x‖ *
                    (‖x‖ ^ (l + 1) *
                      ‖iteratedFDeriv ℝ (n_der - i)
                        (G : (Fin (j + k) → Fin 4 → ℝ) → ℂ) x‖) := by
              rw [mul_assoc, Finset.mul_sum]
              congr 1
              refine Finset.sum_congr rfl (fun i _ => by ring)
          _ ≤ (((m : ℝ) + 1)⁻¹) * C := by
              refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => ?_))
                (inv_nonneg.mpr hm_pos.le)
              have h_di := norm_iteratedFDeriv_concatBumpDiff_le j k m i x
              have h_Gi := SchwartzMap.le_seminorm ℝ (l + 1) (n_der - i) G x
              have h1 : (n_der.choose i : ℝ) * ‖iteratedFDeriv ℝ i d x‖ ≤
                  (n_der.choose i : ℝ) * K_bump i :=
                mul_le_mul_of_nonneg_left h_di (Nat.cast_nonneg _)
              exact mul_le_mul h1 h_Gi
                (mul_nonneg (pow_nonneg (norm_nonneg x) (l + 1)) (norm_nonneg _))
                (mul_nonneg (Nat.cast_nonneg _) (hK_nonneg i))
          _ = C * (((m : ℝ) + 1)⁻¹) := mul_comm _ _
    have h_lim : Tendsto (fun m : ℕ => C * (((m : ℝ) + 1)⁻¹)) Filter.atTop (𝓝 0) := by
      have h_inv : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) Filter.atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp
          (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
      simpa [mul_zero] using (tendsto_const_nhds (x := C)).mul h_inv
    filter_upwards [(tendsto_order.mp h_lim).2 ε hε] with m hm
    rw [SchwartzMap.schwartzSeminormFamily_apply, sub_zero]
    exact (h_bound_m m).trans_lt hm
  simpa using h_sub.add (tendsto_const_nhds (x := G))

theorem positivity_of_compactPositivity
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {W : WightmanFamily ι}
    (hcpos : CompactPositivity S W) :
    Positivity S W := by
  intro N F G hG
  let seq : ℕ → ℂ := fun m =>
    ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α')
            (wightmanConcatSchwartz j k
              (compactCutoff j (F j α) m) (compactCutoff k (F k α') m))
  let limVal : ℂ :=
    ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α') (G j k α α')
  have h_tendsto : Tendsto seq Filter.atTop (𝓝 limVal) := by
    refine tendsto_finsetSum _ (fun j _ =>
      tendsto_finsetSum _ (fun k _ =>
        tendsto_finsetSum _ (fun α _ =>
          tendsto_finsetSum _ (fun α' _ =>
            tendsto_finsetSum _ (fun β _ => ?_)))))
    have h_cat := tendsto_wightmanConcatSchwartz_compactCutoff j k
      (F j α) (F k α') (G j k α α') (hG j k α α')
    have h_W := (W (j + k) (Fin.append (β ∘ Fin.rev) α')).continuous.tendsto
      (G j k α α') |>.comp h_cat
    exact tendsto_const_nhds.mul h_W
  have h_nonneg : ∀ m : ℕ, 0 ≤ seq m := fun m =>
    hcpos N (fun j α => compactCutoff j (F j α) m)
  rw [Complex.nonneg_iff]
  refine ⟨?_, ?_⟩
  · exact ge_of_tendsto (Complex.continuous_re.tendsto limVal |>.comp h_tendsto)
      (Filter.Eventually.of_forall (fun m => (Complex.nonneg_iff.mp (h_nonneg m)).1))
  · have h_im_seq : Complex.im ∘ seq = fun _ => (0 : ℝ) :=
      funext (fun m => ((Complex.nonneg_iff.mp (h_nonneg m)).2).symm)
    have h_im_lim := Complex.continuous_im.tendsto limVal |>.comp h_tendsto
    rw [h_im_seq] at h_im_lim
    exact tendsto_nhds_unique tendsto_const_nhds h_im_lim

theorem positivity_iff_compactPositivity
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι) :
    Positivity S W ↔ CompactPositivity S W :=
  ⟨compactPositivity_of_positivity, positivity_of_compactPositivity⟩

theorem positivity_iff_wightmanKernelPositive_and_hermiticity
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι) :
    Positivity S W ↔
      (WightmanKernelPositive S W ∧ WightmanKernelHermiticity S W) :=
  (positivity_iff_compactPositivity S W).trans
    (compactPositivity_iff_wightmanKernelPositive_and_hermiticity S W)

theorem positivity_of_wightmanPositiveData
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) :
    Positivity S WData.W :=
  positivity_of_compactPositivity (compactPositivity_of_wightmanPositiveData WData)

omit [Fintype ι] [DecidableEq ι] in
theorem wightmanZeroPoint_eq_schwingerFromTube_mul_integral
    {W : WightmanFamily ι} (E : TubeExtension W)
    (f : SchwartzMap (Fin 0 → Fin 4 → ℝ) ℂ) :
    W 0 Fin.elim0 f =
      schwingerFromTube E 0 Fin.elim0 (euclidOrderedBasePoint 0) *
        ∫ x : Fin 0 → Fin 4 → ℝ, f x := by
  have h_bd := E.boundary 0 Fin.elim0 f (euclidTimeVec 1) timeUnitVec_mem_forward_light_cone
  have h_const :
      (fun t : ℝ => ∫ x : Fin 0 → Fin 4 → ℝ,
        E.H 0 Fin.elim0
          (fun i k => (x i k : ℂ) +
            Complex.I * ((t * (i : ℕ) * (euclidTimeVec 1) k : ℝ) : ℂ)) * f x) =
      fun _ : ℝ =>
        schwingerFromTube E 0 Fin.elim0 (euclidOrderedBasePoint 0) *
          ∫ x : Fin 0 → Fin 4 → ℝ, f x := by
    ext t
    have h_arg : ∀ x : Fin 0 → Fin 4 → ℝ,
        (fun (i : Fin 0) (k : Fin 4) => (x i k : ℂ) +
          Complex.I * ((t * (i : ℕ) * (euclidTimeVec 1) k : ℝ) : ℂ)) =
        wickEmbedN 0 (euclidOrderedBasePoint 0) :=
      fun _ => Subsingleton.elim _ _
    simp_rw [h_arg]
    exact MeasureTheory.integral_const_mul _ _
  rw [h_const] at h_bd
  exact tendsto_nhds_unique h_bd tendsto_const_nhds

theorem wightmanKernel_vacuum_eq_schwingerFromTube
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {W : WightmanFamily ι} (E : TubeExtension W) :
    wightmanKernel S W (wightmanVacuumConfig ι) (wightmanVacuumConfig ι) =
      schwingerFromTube E 0 Fin.elim0 (euclidOrderedBasePoint 0) := by
  dsimp only [wightmanVacuumConfig, wightmanBaseConfig]
  rw [wightmanKernel_mk, Finset.univ_unique, Finset.sum_singleton]
  have h_prod : (∏ i : Fin 0, S.C (Fin.elim0 i)
      ((default : Fin 0 → ι) i)) = 1 := Finset.prod_empty
  have h_idx : Fin.append ((default : Fin 0 → ι) ∘ Fin.rev) Fin.elim0 =
      Fin.elim0 := funext (fun i => Fin.elim0 i)
  have h_int_cat :
      (∫ x : Fin 0 → Fin 4 → ℝ,
        (wightmanConcatSchwartz 0 0
          (momentumWavepacketCompactSchwartz 0 0)
          (momentumWavepacketCompactSchwartz 0 0)) x) = 1 := by
    have hc := integral_wightmanConcatSchwartz 0 0
      (momentumWavepacketCompactSchwartz 0 0)
      (momentumWavepacketCompactSchwartz 0 0)
    change (∫ x : Fin 0 → Fin 4 → ℝ,
        (wightmanConcatSchwartz 0 0
          (momentumWavepacketCompactSchwartz 0 0)
          (momentumWavepacketCompactSchwartz 0 0)) x) = _ at hc
    have hm : (∫ y : Fin 0 → Fin 4 → ℝ,
        (momentumWavepacketCompactSchwartz 0 0 :
          SchwartzMap (Fin 0 → Fin 4 → ℝ) ℂ) y) = 1 :=
      integral_momentumWavepacketSchwartz_zero 0
    rw [hc, hm, star_one, one_mul]
  change (∏ i : Fin 0, S.C (Fin.elim0 i) ((default : Fin 0 → ι) i)) *
      W 0 (Fin.append ((default : Fin 0 → ι) ∘ Fin.rev) Fin.elim0)
        (wightmanConcatSchwartz 0 0
          (momentumWavepacketCompactSchwartz 0 0)
          (momentumWavepacketCompactSchwartz 0 0)) = _
  rw [h_prod, one_mul, h_idx, wightmanZeroPoint_eq_schwingerFromTube_mul_integral E,
      h_int_cat, mul_one]

theorem wightmanVacuumNormalized_iff_osVacuumNormalized_of_schwinger_eq
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {W : WightmanFamily ι} (E : TubeExtension W) (𝒮 : SchwingerFamily ι)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = schwingerFromTube E n α x) :
    WightmanVacuumNormalized S W ↔ OSVacuumNormalized 𝒮 := by
  unfold WightmanVacuumNormalized OSVacuumNormalized
  rw [wightmanKernel_vacuum_eq_schwingerFromTube S E,
      ← h_schw 0 Fin.elim0 (euclidOrderedBasePoint 0)
          (euclidOrderedBasePoint_mem_orderedEuclidN 0)]

def wightmanPositiveDataOfWavepacket
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S W A B) :
    WightmanPositiveData R S where
  W := W
  hermiticity A B := by
    rw [← h_ker B A, ← h_ker A B, Complex.star_def, inner_conj_symm]
  positivity Ψ := by
    let v : H := Ψ.sum (fun A c => c • Φ A)
    have h_inner : ⟪v, v⟫_ℂ = wightmanPreInner S W Ψ Ψ := by
      dsimp [v]
      unfold wightmanPreInner
      simp only [Finsupp.sum]
      rw [sum_inner (𝕜 := ℂ)]
      refine Finset.sum_congr rfl (fun A _ => ?_)
      rw [inner_smul_left, inner_sum (𝕜 := ℂ), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun B _ => ?_)
      rw [inner_smul_right, h_ker A B, ← Complex.star_def]
      ring
    rw [← h_inner]
    exact inner_self_nonneg (𝕜 := ℂ)

theorem positivity_of_hilbertWavepacketConfig
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S W A B) :
    Positivity S W :=
  positivity_of_wightmanPositiveData (wightmanPositiveDataOfWavepacket S W Φ h_ker)

noncomputable def wavepacketWightmanPreLM
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H) :
    WightmanPreHilbertSpace WData →ₗ[ℂ] H :=
  (Finsupp.lsum ℂ (fun A => LinearMap.toSpanSingleton ℂ H (Φ A))).comp
    (WightmanPreHilbertSpace.equivFinsupp WData).toLinearMap

@[simp]
lemma wavepacketWightmanPreLM_wightmanBasisPre
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H)
    (A : WightmanConfig ι) :
    wavepacketWightmanPreLM WData Φ (wightmanBasisPre WData A) = Φ A := by
  dsimp [wavepacketWightmanPreLM, wightmanBasisPre, WightmanPreHilbertSpace.equivFinsupp]
  simp

theorem inner_wavepacketWightmanPreLM
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S WData.W A B)
    (Ψ₁ Ψ₂ : WightmanPreHilbertSpace WData) :
    ⟪wavepacketWightmanPreLM WData Φ Ψ₁, wavepacketWightmanPreLM WData Φ Ψ₂⟫_ℂ =
      ⟪Ψ₁, Ψ₂⟫_ℂ := by
  let L := wavepacketWightmanPreLM WData Φ
  have hL : ∀ X : WightmanPreHilbertSpace WData,
      L X = ∑ A ∈ X.toFinsupp.support, X.toFinsupp A • Φ A := by
    intro X
    conv_lhs => rw [wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData X]
    rw [map_finsuppSum]
    unfold Finsupp.sum
    refine Finset.sum_congr rfl (fun A _ => ?_)
    dsimp only
    rw [L.map_smul, wavepacketWightmanPreLM_wightmanBasisPre]
  have hX : ∀ X : WightmanPreHilbertSpace WData,
      X = ∑ A ∈ X.toFinsupp.support, X.toFinsupp A • wightmanBasisPre WData A := by
    intro X
    conv_lhs => rw [wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData X]
    rfl
  rw [hL Ψ₁, hL Ψ₂]
  conv_rhs => rw [hX Ψ₁, hX Ψ₂]
  rw [sum_inner (𝕜 := ℂ), sum_inner (𝕜 := ℂ)]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  rw [inner_smul_left, inner_smul_left, inner_sum (𝕜 := ℂ), inner_sum (𝕜 := ℂ)]
  congr 1
  refine Finset.sum_congr rfl (fun B _ => ?_)
  rw [inner_smul_right, inner_smul_right, h_ker A B, inner_wightmanBasisPre]

theorem norm_wavepacketWightmanPreLM
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S WData.W A B)
    (Ψ : WightmanPreHilbertSpace WData) :
    ‖wavepacketWightmanPreLM WData Φ Ψ‖ = ‖Ψ‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_wavepacketWightmanPreLM WData Φ h_ker Ψ Ψ]

noncomputable def wavepacketWightmanPreCLM
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S WData.W A B) :
    WightmanPreHilbertSpace WData →L[ℂ] H :=
  (wavepacketWightmanPreLM WData Φ).mkContinuous 1 (fun Ψ => by
    rw [one_mul, norm_wavepacketWightmanPreLM WData Φ h_ker Ψ])

noncomputable def wavepacketWightmanCLM
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S WData.W A B) :
    WightmanHilbert WData →L[ℂ] H :=
  (wavepacketWightmanPreCLM WData Φ h_ker).extend (toWightmanHilbert WData)

@[simp]
lemma wavepacketWightmanCLM_toWightmanHilbert
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S WData.W A B)
    (Ψ : WightmanPreHilbertSpace WData) :
    wavepacketWightmanCLM WData Φ h_ker (toWightmanHilbert WData Ψ) =
      wavepacketWightmanPreLM WData Φ Ψ :=
  (wavepacketWightmanPreCLM WData Φ h_ker).extend_eq
    UniformSpace.Completion.isDenseInducing_coe.dense
    (UniformSpace.Completion.isUniformInducing_coe _) Ψ

@[simp]
theorem wavepacketWightmanCLM_wightmanBasis
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S WData.W A B)
    (A : WightmanConfig ι) :
    wavepacketWightmanCLM WData Φ h_ker (wightmanBasis WData A) = Φ A := by
  dsimp [wightmanBasis]
  rw [wavepacketWightmanCLM_toWightmanHilbert, wavepacketWightmanPreLM_wightmanBasisPre]

@[simp]
theorem wavepacketWightmanCLM_wightmanVacuum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S WData.W A B) :
    wavepacketWightmanCLM WData Φ h_ker (wightmanVacuum WData) =
      Φ (wightmanVacuumConfig ι) :=
  wavepacketWightmanCLM_wightmanBasis WData Φ h_ker (wightmanVacuumConfig ι)

theorem inner_wavepacketWightmanCLM
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S WData.W A B)
    (x y : WightmanHilbert WData) :
    ⟪wavepacketWightmanCLM WData Φ h_ker x,
      wavepacketWightmanCLM WData Φ h_ker y⟫_ℂ = ⟪x, y⟫_ℂ := by
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ₁ Ψ₂ =>
    change ⟪wavepacketWightmanCLM WData Φ h_ker (toWightmanHilbert WData Ψ₁),
        wavepacketWightmanCLM WData Φ h_ker (toWightmanHilbert WData Ψ₂)⟫_ℂ =
      ⟪toWightmanHilbert WData Ψ₁, toWightmanHilbert WData Ψ₂⟫_ℂ
    rw [wavepacketWightmanCLM_toWightmanHilbert,
        wavepacketWightmanCLM_toWightmanHilbert,
        inner_toWightmanHilbert,
        inner_wavepacketWightmanPreLM WData Φ h_ker Ψ₁ Ψ₂]

theorem norm_wavepacketWightmanCLM
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S WData.W A B)
    (x : WightmanHilbert WData) :
    ‖wavepacketWightmanCLM WData Φ h_ker x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_wavepacketWightmanCLM WData Φ h_ker x x]

noncomputable def wavepacketWightmanLinearIsometry
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S WData.W A B) :
    WightmanHilbert WData →ₗᵢ[ℂ] H where
  toLinearMap := (wavepacketWightmanCLM WData Φ h_ker).toLinearMap
  norm_map' := norm_wavepacketWightmanCLM WData Φ h_ker

@[simp]
theorem wavepacketWightmanLinearIsometry_wightmanBasis
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S WData.W A B)
    (A : WightmanConfig ι) :
    wavepacketWightmanLinearIsometry WData Φ h_ker (wightmanBasis WData A) = Φ A :=
  wavepacketWightmanCLM_wightmanBasis WData Φ h_ker A

@[simp]
theorem wavepacketWightmanLinearIsometry_wightmanVacuum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S WData.W A B) :
    wavepacketWightmanLinearIsometry WData Φ h_ker (wightmanVacuum WData) =
      Φ (wightmanVacuumConfig ι) :=
  wavepacketWightmanCLM_wightmanVacuum WData Φ h_ker

theorem wavepacketWightmanLinearIsometry_intertwines_translate
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S WData.W A B)
    (U : (Fin 4 → ℝ) → (H →L[ℂ] H))
    (h_U : ∀ (a : Fin 4 → ℝ) (A : WightmanConfig ι),
      Φ (wightmanConfigTranslate a A) = U a (Φ A))
    (a : Fin 4 → ℝ) (x : WightmanHilbert WData) :
    wavepacketWightmanLinearIsometry WData Φ h_ker
        (wightmanTranslate WData htrans a x) =
      U a (wavepacketWightmanLinearIsometry WData Φ h_ker x) := by
  let J := wavepacketWightmanCLM WData Φ h_ker
  change J (wightmanTranslate WData htrans a x) = U a (J x)
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    have h_exp : toWightmanHilbert WData Ψ =
        ∑ A ∈ Ψ.toFinsupp.support, Ψ.toFinsupp A • wightmanBasis WData A := by
      conv_lhs => rw [wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData Ψ]
      rw [map_finsuppSum]
      unfold Finsupp.sum
      refine Finset.sum_congr rfl (fun A _ => (toWightmanHilbert WData).map_smul _ _)
    change J (wightmanTranslate WData htrans a (toWightmanHilbert WData Ψ)) =
      U a (J (toWightmanHilbert WData Ψ))
    rw [h_exp, map_sum, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    rw [map_smul, map_smul, map_smul, map_smul, wightmanTranslate_wightmanBasis]
    dsimp [J]
    rw [wavepacketWightmanCLM_wightmanBasis, wavepacketWightmanCLM_wightmanBasis, h_U]

theorem linearIsometry_surjective_of_denseRange
    {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι_W : E →ₗᵢ[ℂ] H) (hdense : DenseRange ι_W) :
    Function.Surjective ι_W := by
  intro y
  have h_closed : IsClosed (Set.range ι_W) :=
    ι_W.isometry.isUniformInducing.isComplete_range.isClosed
  have h_univ : Set.range ι_W = Set.univ := by
    rw [← h_closed.closure_eq]
    exact hdense.closure_eq
  have hy : y ∈ Set.range ι_W := by
    rw [h_univ]
    trivial
  exact hy

noncomputable def wavepacketWightmanLinearIsometryEquiv
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S WData.W A B)
    (hdense : Dense (↑(Submodule.span ℂ (Set.range Φ)) : Set H)) :
    WightmanHilbert WData ≃ₗᵢ[ℂ] H := by
  let ι_W := wavepacketWightmanLinearIsometry WData Φ h_ker
  have h_sub : (Submodule.span ℂ (Set.range Φ) : Set H) ⊆ Set.range ι_W := by
    have h_le : Submodule.span ℂ (Set.range Φ) ≤ LinearMap.range ι_W.toLinearMap :=
      Submodule.span_le.mpr (by
        rintro _ ⟨A, rfl⟩
        exact ⟨wightmanBasis WData A,
          wavepacketWightmanLinearIsometry_wightmanBasis WData Φ h_ker A⟩)
    exact h_le
  have h_dr : DenseRange ι_W := Dense.mono h_sub hdense
  exact LinearIsometryEquiv.ofSurjective ι_W
    (linearIsometry_surjective_of_denseRange ι_W h_dr)

theorem wightmanVacuumNormalized_of_linearIsometry
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (ι_W : WightmanHilbert WData →ₗᵢ[ℂ] H)
    {Ω : H} (hvac : ι_W (wightmanVacuum WData) = Ω)
    (hnorm : ⟪Ω, Ω⟫_ℂ = 1) :
    WightmanVacuumNormalized S WData.W := by
  unfold WightmanVacuumNormalized
  rw [← inner_wightmanVacuum_self WData, ← ι_W.inner_map_map, hvac, hnorm]

theorem wightmanClusterAlong_of_linearIsometry
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (ι_W : WightmanHilbert WData →ₗᵢ[ℂ] H)
    {Ω : H} (hvac : ι_W (wightmanVacuum WData) = Ω)
    (U : (Fin 4 → ℝ) → (H →L[ℂ] H))
    (h_inter : ∀ (a : Fin 4 → ℝ) (x : WightmanHilbert WData),
      ι_W (wightmanTranslate WData htrans a x) = U a (ι_W x))
    {a : Fin 4 → ℝ}
    (h_cluster : ∀ x y : H,
      Tendsto (fun t : ℝ => ⟪x, U (t • a) y⟫_ℂ) Filter.atTop
        (𝓝 (⟪x, Ω⟫_ℂ * ⟪Ω, y⟫_ℂ))) :
    WightmanClusterAlong WData a := by
  intro A B
  have h_eq : (fun t : ℝ =>
      wightmanKernel S WData.W A (wightmanConfigTranslate (t • a) B)) =
      fun t : ℝ => ⟪ι_W (wightmanBasis WData A), U (t • a) (ι_W (wightmanBasis WData B))⟫_ℂ := by
    ext t
    rw [← inner_wightmanBasis WData A (wightmanConfigTranslate (t • a) B),
        ← wightmanTranslate_wightmanBasis WData htrans (t • a) B,
        ← ι_W.inner_map_map, h_inter]
  have h_lim_eq :
      wightmanKernel S WData.W A (wightmanVacuumConfig ι) *
        wightmanKernel S WData.W (wightmanVacuumConfig ι) B =
      ⟪ι_W (wightmanBasis WData A), Ω⟫_ℂ * ⟪Ω, ι_W (wightmanBasis WData B)⟫_ℂ := by
    rw [← inner_wightmanBasis_wightmanVacuum WData A,
        ← inner_wightmanVacuum_wightmanBasis WData B,
        ← hvac, ι_W.inner_map_map, ι_W.inner_map_map]
  rw [h_eq, h_lim_eq]
  exact h_cluster (ι_W (wightmanBasis WData A)) (ι_W (wightmanBasis WData B))

theorem wightmanVacuumUnique_of_linearIsometry
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (ι_W : WightmanHilbert WData →ₗᵢ[ℂ] H)
    {Ω : H} (hvac : ι_W (wightmanVacuum WData) = Ω)
    (U : (Fin 4 → ℝ) → (H →L[ℂ] H))
    (h_inter : ∀ (a : Fin 4 → ℝ) (x : WightmanHilbert WData),
      ι_W (wightmanTranslate WData htrans a x) = U a (ι_W x))
    (h_uniq : ∀ v : H, (∀ a : Fin 4 → ℝ, U a v = v) → v = ⟪Ω, v⟫_ℂ • Ω) :
    WightmanVacuumUnique WData htrans := by
  intro Ψ hfixed
  apply ι_W.injective
  have hU_fixed : ∀ a : Fin 4 → ℝ, U a (ι_W Ψ) = ι_W Ψ := fun a => by
    rw [← h_inter a Ψ, hfixed a]
  have h_eq := h_uniq (ι_W Ψ) hU_fixed
  rw [← hvac, ι_W.inner_map_map, ← ι_W.map_smul] at h_eq
  exact h_eq

theorem eq_zero_on_rightHalfPlane_of_imag_zero {g : ℂ → ℂ}
    (hg_holo : DifferentiableOn ℂ g {z : ℂ | 0 < z.re})
    (hg_cont : ContinuousOn g rightHalfPlane)
    (hg_imag : ∀ t : ℝ, g (Complex.I * (t : ℂ)) = 0) :
    ∀ z ∈ rightHalfPlane, g z = 0 := by
  let f : ℂ → ℂ := fun w => if 0 ≤ w.im then g (-Complex.I * w) else 0
  have h_slit : Analysis.slitDomain (Set.univ : Set ℝ) = Set.univ := by
    ext w
    simp [Analysis.slitDomain]
  have h_rot_mem : ∀ {w : ℂ}, 0 ≤ w.im → -Complex.I * w ∈ rightHalfPlane := by
    intro w hw
    change 0 ≤ (-Complex.I * w).re
    simpa [Complex.mul_re] using hw
  have h_rot_real : ∀ w : ℂ, w.im = 0 → g (-Complex.I * w) = 0 := by
    intro w hw
    have hw_eq : -Complex.I * w = Complex.I * ((-w.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hw]
    rw [hw_eq]
    exact hg_imag (-w.re)
  have hf_cont : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro w₀
    by_cases hpos : 0 < w₀.im
    · have h_ev : f =ᶠ[𝓝 w₀] fun w => g (-Complex.I * w) := by
        filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hpos]
          with w hw
        exact if_pos (le_of_lt hw)
      have h_nhds : rightHalfPlane ∈ 𝓝 (-Complex.I * w₀) :=
        Filter.mem_of_superset
          ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
            (show (0 : ℝ) < (-Complex.I * w₀).re by simp [Complex.mul_re, hpos]))
          (fun z (hz : 0 < z.re) => (le_of_lt hz : z ∈ rightHalfPlane))
      have hg_at : ContinuousAt g (-Complex.I * w₀) :=
        hg_cont.continuousAt h_nhds
      exact (hg_at.comp (continuous_const.mul continuous_id).continuousAt).congr h_ev.symm
    · by_cases hneg : w₀.im < 0
      · have h_ev : f =ᶠ[𝓝 w₀] fun _ => (0 : ℂ) := by
          filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hneg]
            with w hw
          exact if_neg (not_le_of_gt hw)
        exact continuousAt_const.congr h_ev.symm
      · have hw0 : w₀.im = 0 := le_antisymm (not_lt.mp hpos) (not_lt.mp hneg)
        have hfw0 : f w₀ = 0 := by
          dsimp [f]
          rw [if_pos (le_of_eq hw0.symm)]
          exact h_rot_real w₀ hw0
        rw [Metric.continuousAt_iff]
        intro ε hε
        have hg_within : ContinuousWithinAt (fun w : ℂ => g (-Complex.I * w))
            {w : ℂ | 0 ≤ w.im} w₀ :=
          (hg_cont.comp (continuous_const.mul continuous_id).continuousOn
            (fun _ hw => h_rot_mem hw)).continuousWithinAt (le_of_eq hw0.symm)
        rw [Metric.continuousWithinAt_iff] at hg_within
        rcases hg_within ε hε with ⟨δ, hδ_pos, hδ⟩
        refine ⟨δ, hδ_pos, fun w hw_dist => ?_⟩
        rw [hfw0]
        dsimp [f]
        split_ifs with hw_im
        · have h_step := hδ hw_im hw_dist
          rwa [h_rot_real w₀ hw0] at h_step
        · simpa using hε
  have hf_ana_pos : AnalyticOn ℂ f Analysis.upperHalfPlane := by
    have h_open_uhp : IsOpen Analysis.upperHalfPlane :=
      isOpen_lt continuous_const Complex.continuous_im
    refine DifferentiableOn.analyticOn ?_ h_open_uhp
    have h_diff_comp : DifferentiableOn ℂ (fun w : ℂ => g (-Complex.I * w))
        Analysis.upperHalfPlane :=
      hg_holo.comp (differentiable_const (-Complex.I) |>.mul differentiable_id).differentiableOn
        (fun w hw => by
          have hw' : 0 < w.im := hw
          change 0 < (-Complex.I * w).re
          simpa [Complex.mul_re] using hw')
    exact h_diff_comp.congr (fun w hw => if_pos (le_of_lt hw))
  have hf_ana_neg : AnalyticOn ℂ f Analysis.lowerHalfPlane := by
    have h_open_lhp : IsOpen Analysis.lowerHalfPlane :=
      isOpen_lt Complex.continuous_im continuous_const
    refine DifferentiableOn.analyticOn ?_ h_open_lhp
    exact (differentiableOn_const (0 : ℂ)).congr
      (fun w hw => if_neg (not_le_of_gt hw))
  have hf_ana_univ : AnalyticOnNhd ℂ f Set.univ := by
    have h_on : AnalyticOn ℂ f (Analysis.slitDomain (Set.univ : Set ℝ)) :=
      Analysis.eow_1d_continuous Set.univ isOpen_univ f
        hf_cont.continuousOn hf_ana_pos hf_ana_neg
    rw [h_slit] at h_on
    exact isOpen_univ.analyticOn_iff_analyticOnNhd.mp h_on
  have hf_ev_zero : f =ᶠ[𝓝 (-Complex.I)] 0 := by
    have h_mem : Analysis.lowerHalfPlane ∈ 𝓝 (-Complex.I) :=
      (isOpen_lt Complex.continuous_im continuous_const).mem_nhds (by simp)
    filter_upwards [h_mem] with w hw
    exact if_neg (not_le_of_gt hw)
  have hf_all_zero : Set.EqOn f 0 Set.univ :=
    hf_ana_univ.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ (-Complex.I)) hf_ev_zero
  intro z hz
  have hz' : 0 ≤ z.re := hz
  have hz_im : 0 ≤ (Complex.I * z).im := by
    simpa [Complex.mul_im] using hz'
  have h_eval : f (Complex.I * z) = 0 := hf_all_zero (Set.mem_univ (Complex.I * z))
  dsimp [f] at h_eval
  rw [if_pos hz_im] at h_eval
  have h_mul : -Complex.I * (Complex.I * z) = z := by
    rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
  rwa [h_mul] at h_eval

def OSHolomorphicSemigroup.IsWeaklyHolomorphic
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D}
    (ℰ : OSHolomorphicSemigroup D hcontr) : Prop :=
  ∀ χ Ψ : OSHilbert D, ∃ F : ℂ → ℂ,
    (∀ (z : ℂ) (hz : z ∈ rightHalfPlane), F z = ⟪χ, ℰ.Z z hz Ψ⟫_ℂ) ∧
    ContinuousOn F rightHalfPlane ∧
    DifferentiableOn ℂ F {z : ℂ | 0 < z.re}

theorem OSSpectralDecomposition.isWeaklyHolomorphic_toOSHolomorphicSemigroup
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D} {m : ℕ}
    (spec : OSSpectralDecomposition D hcontr m) :
    spec.toOSHolomorphicSemigroup.IsWeaklyHolomorphic := by
  intro χ Ψ
  refine ⟨fun z => ∑ k : Fin m, laplaceExp (spec.E k) z * ⟪χ, spec.P k Ψ⟫_ℂ,
    fun z _ => ?_, ?_, ?_⟩
  · change (∑ k : Fin m, laplaceExp (spec.E k) z * ⟪χ, spec.P k Ψ⟫_ℂ) =
      ⟪χ, spec.entireZ z Ψ⟫_ℂ
    rw [spec.entireZ_apply, inner_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [inner_smul_right]
  · have h_diff : Differentiable ℂ
        (fun z : ℂ => ∑ k : Fin m, laplaceExp (spec.E k) z * ⟪χ, spec.P k Ψ⟫_ℂ) := by
      have h_term : ∀ k : Fin m,
          Differentiable ℂ (fun z : ℂ => laplaceExp (spec.E k) z * ⟪χ, spec.P k Ψ⟫_ℂ) :=
        fun k => (differentiable_laplaceExp (spec.E k)).mul (differentiable_const _)
      fun_prop
    exact h_diff.continuous.continuousOn
  · have h_diff : Differentiable ℂ
        (fun z : ℂ => ∑ k : Fin m, laplaceExp (spec.E k) z * ⟪χ, spec.P k Ψ⟫_ℂ) := by
      have h_term : ∀ k : Fin m,
          Differentiable ℂ (fun z : ℂ => laplaceExp (spec.E k) z * ⟪χ, spec.P k Ψ⟫_ℂ) :=
        fun k => (differentiable_laplaceExp (spec.E k)).mul (differentiable_const _)
      fun_prop
    exact h_diff.differentiableOn

lemma mul_exp_neg_mul_le_inv_of_nonneg {E r u : ℝ}
    (hE : 0 ≤ E) (hr : 0 < r) (hru : r ≤ u) :
    E * Real.exp (-(E * u)) ≤ r⁻¹ := by
  have h1 : E * r ≤ Real.exp (E * r) :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp (E * r))
  have h2 : Real.exp (-(E * u)) ≤ Real.exp (-(E * r)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hru hE))
  have h3 : E * Real.exp (-(E * r)) ≤ r⁻¹ := by
    calc E * Real.exp (-(E * r))
        = r⁻¹ * ((E * r) * Real.exp (-(E * r))) := by
          field_simp [hr.ne']
      _ ≤ r⁻¹ * (Real.exp (E * r) * Real.exp (-(E * r))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le)
            (inv_nonneg.mpr hr.le)
      _ = r⁻¹ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  exact (mul_le_mul_of_nonneg_left h2 hE).trans h3

theorem OSSpectralMeasure.isWeaklyHolomorphic_toOSHolomorphicSemigroupOfBochner
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D}
    {A : Type*} [MeasurableSpace A]
    (M : OSSpectralMeasure D hcontr A)
    (hE_meas : Measurable M.E)
    (Z : ℂ → (OSHilbert D →L[ℂ] OSHilbert D))
    (h_eq : ∀ (z : ℂ), z ∈ rightHalfPlane → ∀ x : OSHilbert D, Z z x = M.bochnerZ z x)
    (h_int : ∀ (z : ℂ), z ∈ rightHalfPlane → ∀ x : OSHilbert D,
      Integrable (fun a : A => laplaceExp (M.E a) z • M.P a x) M.μ)
    (h_add : ∀ (z₁ z₂ : ℂ), z₁ ∈ rightHalfPlane → z₂ ∈ rightHalfPlane →
      Z (z₁ + z₂) = (Z z₁).comp (Z z₂))
    (h_vac : ∀ (z : ℂ), z ∈ rightHalfPlane → M.bochnerZ z (osVacuum D) = osVacuum D)
    (h_contr : ∀ (z : ℂ), z ∈ rightHalfPlane → ∀ x : OSHilbert D,
      ‖M.bochnerZ z x‖ ≤ ‖x‖) :
    (M.toOSHolomorphicSemigroupOfBochner Z h_eq h_int h_add h_vac h_contr).IsWeaklyHolomorphic := by
  intro χ Ψ
  let g : A → ℂ := fun a => ⟪χ, M.P a Ψ⟫_ℂ
  have hg_int : Integrable g M.μ := by
    have h0 := (OSSpectralMeasure.innerRightCLM (D := D) χ).integrable_comp
      (h_int 0 zero_mem_rightHalfPlane Ψ)
    simpa [g, laplaceExp_zero_right] using h0
  have h_meas_F : ∀ z : ℂ,
      AEStronglyMeasurable (fun a : A => laplaceExp (M.E a) z * g a) M.μ := by
    intro z
    have h_lap_meas : Measurable (fun a : A => laplaceExp (M.E a) z) := by
      unfold laplaceExp
      exact (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).measurable.comp hE_meas
    exact h_lap_meas.aestronglyMeasurable.mul hg_int.aestronglyMeasurable
  let F : ℂ → ℂ := fun z => ∫ a : A, laplaceExp (M.E a) z * g a ∂M.μ
  refine ⟨F, fun z hz => ?_, ?_, ?_⟩
  · change F z = ⟪χ, Z z Ψ⟫_ℂ
    rw [h_eq z hz Ψ, M.inner_bochnerZ_right z Ψ χ (h_int z hz Ψ)]
  · refine MeasureTheory.continuousOn_of_dominated
      (fun z _ => h_meas_F z)
      (fun z hz => Filter.Eventually.of_forall
        (fun a => M.norm_laplaceExp_mul_inner_proj_le_half_add_norm_sq hz a χ Ψ))
      (M.integrable_half_add_norm_sq χ Ψ)
      (Filter.Eventually.of_forall (fun a =>
        ((differentiable_laplaceExp (M.E a)).continuous.mul continuous_const).continuousOn))
  · intro z₀ hz₀
    have hz₀_pos : 0 < z₀.re := hz₀
    let r : ℝ := z₀.re / 2
    have hr_pos : 0 < r := half_pos hz₀_pos
    let s : Set ℂ := Metric.ball z₀ r
    have hs_nhds : s ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hr_pos
    have hs_re : ∀ z ∈ s, r ≤ z.re := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have h_abs : |z.re - z₀.re| < r :=
        (Complex.abs_re_le_norm (z - z₀)).trans_lt hz
      have h_low := (abs_lt.mp h_abs).1
      dsimp [r] at h_low ⊢
      linarith
    let F' : ℂ → A → ℂ := fun z a => (-(M.E a : ℂ) * laplaceExp (M.E a) z) * g a
    have hF'_meas : AEStronglyMeasurable (F' z₀) M.μ := by
      have hE_c : Measurable (fun a : A => -(M.E a : ℂ)) :=
        (continuous_neg.comp Complex.continuous_ofReal).measurable.comp hE_meas
      have h_eq' : F' z₀ = fun a => (-(M.E a : ℂ)) * (laplaceExp (M.E a) z₀ * g a) := by
        ext a
        dsimp [F']
        ring
      rw [h_eq']
      exact hE_c.aestronglyMeasurable.mul (h_meas_F z₀)
    let bound : A → ℝ := fun a => r⁻¹ * ((‖M.P a χ‖ ^ 2 + ‖M.P a Ψ‖ ^ 2) / 2)
    have h_bound_int : Integrable bound M.μ :=
      (M.integrable_half_add_norm_sq χ Ψ).const_mul r⁻¹
    have h_bound : ∀ᵐ a : A ∂M.μ, ∀ z ∈ s, ‖F' z a‖ ≤ bound a := by
      refine Filter.Eventually.of_forall (fun a z hz => ?_)
      have h_lap_norm : ‖-(M.E a : ℂ) * laplaceExp (M.E a) z‖ ≤ r⁻¹ := by
        have h_exp_arg : -z.re * M.E a = -(M.E a * z.re) := by ring
        rw [norm_mul, norm_neg, Complex.norm_real,
            Real.norm_of_nonneg (M.energy_nonneg a), norm_laplaceExp, h_exp_arg]
        exact mul_exp_neg_mul_le_inv_of_nonneg (M.energy_nonneg a) hr_pos (hs_re z hz)
      have h_g := M.norm_inner_proj_le_half_add_norm_sq a χ Ψ
      dsimp [F', bound]
      rw [norm_mul]
      exact mul_le_mul h_lap_norm h_g (norm_nonneg _) (inv_nonneg.mpr hr_pos.le)
    have h_diff : ∀ᵐ a : A ∂M.μ, ∀ z ∈ s,
        HasDerivAt (fun w => laplaceExp (M.E a) w * g a) (F' z a) z := by
      refine Filter.Eventually.of_forall (fun a z _ => ?_)
      have h_lin : HasDerivAt (fun w : ℂ => -w * (M.E a : ℂ))
          (-1 * (M.E a : ℂ)) z :=
        (hasDerivAt_id z).neg.mul_const (M.E a : ℂ)
      have h_exp : HasDerivAt (laplaceExp (M.E a))
          (laplaceExp (M.E a) z * (-1 * (M.E a : ℂ))) z :=
        h_lin.cexp
      have h_mul := h_exp.mul_const (g a)
      have h_eq_d : (laplaceExp (M.E a) z * (-1 * (M.E a : ℂ))) * g a = F' z a := by
        dsimp [F']
        ring
      rwa [h_eq_d] at h_mul
    have hz₀_rhp : z₀ ∈ rightHalfPlane := le_of_lt hz₀_pos
    have hF_z₀_int : Integrable (fun a : A => laplaceExp (M.E a) z₀ * g a) M.μ :=
      (M.integrable_half_add_norm_sq χ Ψ).mono' (h_meas_F z₀)
        (Filter.Eventually.of_forall
          (fun a => M.norm_laplaceExp_mul_inner_proj_le_half_add_norm_sq hz₀_rhp a χ Ψ))
    have h_deriv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      hs_nhds (Filter.Eventually.of_forall h_meas_F) hF_z₀_int hF'_meas
      h_bound h_bound_int h_diff).2
    exact h_deriv.differentiableAt.differentiableWithinAt

theorem OSContinuousSpectralData.isWeaklyHolomorphic
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D}
    {Ω : Type*} [MeasurableSpace Ω]
    (M : OSContinuousSpectralData D hcontr Ω) :
    M.ℰ.IsWeaklyHolomorphic := by
  intro χ Ψ
  let g : Ω → ℂ := fun a => star (M.wave χ a) * M.wave Ψ a
  have hg_int : Integrable g M.μ := M.integrable_star_wave_mul χ Ψ
  have h_meas_F : ∀ z : ℂ,
      AEStronglyMeasurable (fun a : Ω => laplaceExp (M.E a) z * g a) M.μ := by
    intro z
    have h_lap_meas : Measurable (fun a : Ω => laplaceExp (M.E a) z) := by
      unfold laplaceExp
      exact (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).measurable.comp M.measurable_E
    exact h_lap_meas.aestronglyMeasurable.mul hg_int.aestronglyMeasurable
  let F : ℂ → ℂ := fun z => ∫ a : Ω, laplaceExp (M.E a) z * g a ∂M.μ
  refine ⟨F, fun z hz => (M.semigroup_inner_eq z hz χ Ψ).symm, ?_, ?_⟩
  · refine MeasureTheory.continuousOn_of_dominated
      (fun z _ => h_meas_F z)
      (fun z hz => Filter.Eventually.of_forall
        (fun a => M.norm_laplaceExp_mul_wave_le_half_add_norm_sq hz a χ Ψ))
      (M.integrable_half_add_norm_sq χ Ψ)
      (Filter.Eventually.of_forall (fun a =>
        ((differentiable_laplaceExp (M.E a)).continuous.mul continuous_const).continuousOn))
  · intro z₀ hz₀
    have hz₀_pos : 0 < z₀.re := hz₀
    let r : ℝ := z₀.re / 2
    have hr_pos : 0 < r := half_pos hz₀_pos
    let s : Set ℂ := Metric.ball z₀ r
    have hs_nhds : s ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hr_pos
    have hs_re : ∀ z ∈ s, r ≤ z.re := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have h_abs : |z.re - z₀.re| < r :=
        (Complex.abs_re_le_norm (z - z₀)).trans_lt hz
      have h_low := (abs_lt.mp h_abs).1
      dsimp [r] at h_low ⊢
      linarith
    let F' : ℂ → Ω → ℂ := fun z a => (-(M.E a : ℂ) * laplaceExp (M.E a) z) * g a
    have hF'_meas : AEStronglyMeasurable (F' z₀) M.μ := by
      have hE_c : Measurable (fun a : Ω => -(M.E a : ℂ)) :=
        (continuous_neg.comp Complex.continuous_ofReal).measurable.comp M.measurable_E
      have h_eq' : F' z₀ = fun a => (-(M.E a : ℂ)) * (laplaceExp (M.E a) z₀ * g a) := by
        ext a
        dsimp [F']
        ring
      rw [h_eq']
      exact hE_c.aestronglyMeasurable.mul (h_meas_F z₀)
    let bound : Ω → ℝ := fun a => r⁻¹ * ((‖M.wave χ a‖ ^ 2 + ‖M.wave Ψ a‖ ^ 2) / 2)
    have h_bound_int : Integrable bound M.μ :=
      (M.integrable_half_add_norm_sq χ Ψ).const_mul r⁻¹
    have h_bound : ∀ᵐ a : Ω ∂M.μ, ∀ z ∈ s, ‖F' z a‖ ≤ bound a := by
      refine Filter.Eventually.of_forall (fun a z hz => ?_)
      have h_lap_norm : ‖-(M.E a : ℂ) * laplaceExp (M.E a) z‖ ≤ r⁻¹ := by
        have h_exp_arg : -z.re * M.E a = -(M.E a * z.re) := by ring
        rw [norm_mul, norm_neg, Complex.norm_real,
            Real.norm_of_nonneg (M.energy_nonneg a), norm_laplaceExp, h_exp_arg]
        exact mul_exp_neg_mul_le_inv_of_nonneg (M.energy_nonneg a) hr_pos (hs_re z hz)
      have h_g := M.norm_star_wave_mul_le_half_add_norm_sq a χ Ψ
      dsimp [F', bound]
      rw [norm_mul]
      exact mul_le_mul h_lap_norm h_g (norm_nonneg _) (inv_nonneg.mpr hr_pos.le)
    have h_diff : ∀ᵐ a : Ω ∂M.μ, ∀ z ∈ s,
        HasDerivAt (fun w => laplaceExp (M.E a) w * g a) (F' z a) z := by
      refine Filter.Eventually.of_forall (fun a z _ => ?_)
      have h_lin : HasDerivAt (fun w : ℂ => -w * (M.E a : ℂ))
          (-1 * (M.E a : ℂ)) z :=
        (hasDerivAt_id z).neg.mul_const (M.E a : ℂ)
      have h_exp : HasDerivAt (laplaceExp (M.E a))
          (laplaceExp (M.E a) z * (-1 * (M.E a : ℂ))) z :=
        h_lin.cexp
      have h_mul := h_exp.mul_const (g a)
      have h_eq_d : (laplaceExp (M.E a) z * (-1 * (M.E a : ℂ))) * g a = F' z a := by
        dsimp [F']
        ring
      rwa [h_eq_d] at h_mul
    have hz₀_rhp : z₀ ∈ rightHalfPlane := le_of_lt hz₀_pos
    have hF_z₀_int : Integrable (fun a : Ω => laplaceExp (M.E a) z₀ * g a) M.μ :=
      (M.integrable_half_add_norm_sq χ Ψ).mono' (h_meas_F z₀)
        (Filter.Eventually.of_forall
          (fun a => M.norm_laplaceExp_mul_wave_le_half_add_norm_sq hz₀_rhp a χ Ψ))
    have h_deriv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      hs_nhds (Filter.Eventually.of_forall h_meas_F) hF_z₀_int hF'_meas
      h_bound h_bound_int h_diff).2
    exact h_deriv.differentiableAt.differentiableWithinAt

theorem osContractionSemigroup_fixed_of_realTimeUnitary_fixed
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D}
    (ℰ : OSHolomorphicSemigroup D hcontr)
    (h_holo : ℰ.IsWeaklyHolomorphic)
    {Ψ : OSHilbert D}
    (hfixed : ∀ t : ℝ, ℰ.realTimeUnitary t Ψ = Ψ)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    osContractionSemigroup D hcontr τ hτ Ψ = Ψ := by
  apply ext_inner_left ℂ
  intro χ
  rcases h_holo χ Ψ with ⟨F, hF_eq, hF_cont, hF_diff⟩
  let g : ℂ → ℂ := fun z => F z - ⟪χ, Ψ⟫_ℂ
  have hg_holo : DifferentiableOn ℂ g {z : ℂ | 0 < z.re} :=
    hF_diff.sub (differentiableOn_const _)
  have hg_cont : ContinuousOn g rightHalfPlane :=
    hF_cont.sub continuousOn_const
  have hg_imag : ∀ t : ℝ, g (Complex.I * (t : ℂ)) = 0 := by
    intro t
    dsimp [g]
    rw [hF_eq (Complex.I * (t : ℂ)) (mul_I_mem_rightHalfPlane t)]
    change ⟪χ, ℰ.realTimeUnitary t Ψ⟫_ℂ - ⟪χ, Ψ⟫_ℂ = 0
    rw [hfixed t, sub_self]
  have hτ_zero := eq_zero_on_rightHalfPlane_of_imag_zero hg_holo hg_cont hg_imag
    (τ : ℂ) (ofReal_mem_rightHalfPlane hτ)
  dsimp [g] at hτ_zero
  rw [hF_eq (τ : ℂ) (ofReal_mem_rightHalfPlane hτ), ℰ.real_eq τ hτ] at hτ_zero
  exact sub_eq_zero.mp hτ_zero

theorem eq_smul_osVacuum_of_spacetimeTranslate_fixed
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D}
    (ℰ : OSHolomorphicSemigroup D hcontr)
    (h_holo : ℰ.IsWeaklyHolomorphic)
    (htrans : OSTranslationInvariant D.𝒮)
    (hcluster : OSTimeClusterDecomposition D)
    {Ψ : OSHilbert D}
    (hfixed : ∀ a : Fin 4 → ℝ, ℰ.spacetimeTranslate htrans a Ψ = Ψ) :
    Ψ = ⟪osVacuum D, Ψ⟫_ℂ • osVacuum D := by
  have h_rt : ∀ t : ℝ, ℰ.realTimeUnitary t Ψ = Ψ := by
    intro t
    have h_a := hfixed (euclidTimeVec t)
    unfold OSHolomorphicSemigroup.spacetimeTranslate at h_a
    have h_sp : spatialPart (euclidTimeVec t) = 0 := by
      ext i
      simp [spatialPart, euclidTimeVec]
    have h_t0 : euclidTimeVec t 0 = t := rfl
    rw [h_sp, h_t0, ContinuousLinearMap.comp_apply, osSpatialTranslate_zero,
        ContinuousLinearMap.id_apply] at h_a
    exact h_a
  exact eq_smul_osVacuum_of_osContractionSemigroup_fixed D hcontr hcluster
    (osContractionSemigroup_fixed_of_realTimeUnitary_fixed ℰ h_holo h_rt)

structure GeneralWightmanAxiomsWithUniqueVacuum
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) extends
    WightmanAxioms R S η where
  vacuumNormalized : WightmanVacuumNormalized S WData.W
  vacuumUnique :
    WightmanVacuumUnique WData
      (wightmanTranslationInvariant_of_poincare R poincare)

namespace ForwardConeOSReconstructedWightman

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

noncomputable def toGeneralWightmanAxiomsWithUniqueVacuumOfWavepacket
    (P : ForwardConeOSReconstructedWightman R S η 𝒮)
    (h_holo : P.semigroup.IsWeaklyHolomorphic)
    (hnorm : OSVacuumNormalized 𝒮)
    (hcluster : OSTimeClusterDecomposition P.osData)
    (Φ : WightmanConfig ι → P.Hilbert)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S P.W A B)
    (h_vac : Φ (wightmanVacuumConfig ι) = P.vacuum)
    (h_trans : ∀ (a : Fin 4 → ℝ) (A : WightmanConfig ι),
      Φ (wightmanConfigTranslate a A) =
        P.semigroup.spacetimeTranslate P.osAxioms.os1_translation (euclidTimeReflect a) (Φ A)) :
    GeneralWightmanAxiomsWithUniqueVacuum R S η where
  toWightmanAxioms := P.toWightmanAxioms
  vacuumNormalized :=
    (wightmanVacuumNormalized_iff_osVacuumNormalized_of_schwinger_eq S P.E 𝒮
      P.schwinger_eq).mpr hnorm
  vacuumUnique :=
    let htr := wightmanTranslationInvariant_of_poincare R P.poincare
    let ι_W := wavepacketWightmanLinearIsometry P.toWightmanPositiveData Φ h_ker
    let U : (Fin 4 → ℝ) → P.Hilbert →L[ℂ] P.Hilbert :=
      fun a => P.semigroup.spacetimeTranslate P.osAxioms.os1_translation (euclidTimeReflect a)
    wightmanVacuumUnique_of_linearIsometry P.toWightmanPositiveData htr ι_W
      ((wavepacketWightmanLinearIsometry_wightmanVacuum
        P.toWightmanPositiveData Φ h_ker).trans h_vac)
      U
      (wavepacketWightmanLinearIsometry_intertwines_translate
        P.toWightmanPositiveData htr Φ h_ker U h_trans)
      (fun _ hfixed => eq_smul_osVacuum_of_spacetimeTranslate_fixed
        P.semigroup h_holo P.osAxioms.os1_translation hcluster
        (fun a => by
          have h := hfixed (euclidTimeReflect a)
          dsimp [U] at h
          rwa [euclidTimeReflect_involutive] at h))

end ForwardConeOSReconstructedWightman

namespace OSReconstructionData

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}
  {hOS : OSAxioms R S η 𝒮}
  {hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData}

noncomputable def toGeneralWightmanAxiomsWithUniqueVacuum
    (G : OSReconstructionData hOS hcluster)
    (hnorm : OSVacuumNormalized 𝒮)
    (Φ : WightmanConfig ι → OSHilbert hOS.toReflectionPositiveData)
    (h_ker : ∀ A B : WightmanConfig ι,
      ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S G.F.toWightmanFamily A B)
    (h_vac : Φ (wightmanVacuumConfig ι) = osVacuum hOS.toReflectionPositiveData)
    (h_trans : ∀ (a : Fin 4 → ℝ) (A : WightmanConfig ι),
      Φ (wightmanConfigTranslate a A) =
        G.toOSHolomorphicSemigroup.spacetimeTranslate hOS.os1_translation
          (euclidTimeReflect a) (Φ A)) :
    GeneralWightmanAxiomsWithUniqueVacuum R S η :=
  G.toForwardConeOSReconstructedWightman.toGeneralWightmanAxiomsWithUniqueVacuumOfWavepacket
    G.spec.isWeaklyHolomorphic_toOSHolomorphicSemigroup
    hnorm hcluster Φ h_ker h_vac h_trans

end OSReconstructionData

namespace OSMeasureReconstructionData

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}
  {hOS : OSAxioms R S η 𝒮}
  {hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData}

noncomputable def toWightmanAxioms
    (G : OSMeasureReconstructionData hOS hcluster) :
    WightmanAxioms R S η :=
  G.toForwardConeOSReconstructedWightman.toWightmanAxioms

noncomputable def toGeneralWightmanAxiomsWithUniqueVacuum
    (G : OSMeasureReconstructionData hOS hcluster)
    (hnorm : OSVacuumNormalized 𝒮)
    (Φ : WightmanConfig ι → OSHilbert hOS.toReflectionPositiveData)
    (h_ker : ∀ A B : WightmanConfig ι,
      ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S G.F.toWightmanFamily A B)
    (h_vac : Φ (wightmanVacuumConfig ι) = osVacuum hOS.toReflectionPositiveData)
    (h_trans : ∀ (a : Fin 4 → ℝ) (A : WightmanConfig ι),
      Φ (wightmanConfigTranslate a A) =
        G.toOSHolomorphicSemigroup.spacetimeTranslate hOS.os1_translation
          (euclidTimeReflect a) (Φ A)) :
    GeneralWightmanAxiomsWithUniqueVacuum R S η :=
  G.toForwardConeOSReconstructedWightman.toGeneralWightmanAxiomsWithUniqueVacuumOfWavepacket
    G.spec.isWeaklyHolomorphic
    hnorm hcluster Φ h_ker h_vac h_trans

end OSMeasureReconstructionData

end
end QFT
