import WightmanFramework

namespace QFT

noncomputable section

lemma zpow_neg_one_permInversions :
    ∀ {n : ℕ} (σ : Equiv.Perm (Fin n)),
      ((-1 : ℤ) ^ permInversions σ) = (Equiv.Perm.sign σ : ℤ) := by
  intro n σ
  have h_ind : ∀ (m : ℕ) (τ : Equiv.Perm (Fin n)),
      permInversions τ = m → ((-1 : ℤ) ^ m) = (Equiv.Perm.sign τ : ℤ) := by
    intro m
    induction m with
    | zero =>
      intro τ h0
      have hτ : τ = 1 := perm_eq_one_of_permInversions_zero h0
      subst hτ
      simp
    | succ k ih =>
      intro τ hk
      have hpos : 0 < permInversions τ := by omega
      rcases exists_adjacent_inversion_of_pos hpos with ⟨i, hi, hinv⟩
      let i' : Fin n := ⟨i.val + 1, hi⟩
      let s : Equiv.Perm (Fin n) := Equiv.swap i i'
      have hs_eq := permInversions_mul_adjacent_swap τ i hi hinv
      have hk' : permInversions (τ * s) = k := by
        dsimp [s, i'] at hs_eq ⊢
        omega
      have ih_val := ih (τ * s) hk'
      have hne : i ≠ i' := by
        intro h_eq
        have hv := congrArg Fin.val h_eq
        dsimp [i'] at hv
        omega
      have hsign_s : Equiv.Perm.sign s = -1 := Equiv.Perm.sign_swap hne
      have h_tau : τ = (τ * s) * s := by
        ext x
        simp [s]
      rw [h_tau, map_mul, hsign_s]
      push_cast
      rw [← ih_val, pow_succ]
  exact h_ind (permInversions σ) σ rfl

lemma eta_sq_eq_one {η : ℂ} (hη : η = 1 ∨ η = -1) : η ^ 2 = 1 := by
  rcases hη with rfl | rfl <;> norm_num

lemma eta_ne_zero {η : ℂ} (hη : η = 1 ∨ η = -1) : η ≠ 0 := by
  rcases hη with rfl | rfl <;> norm_num

lemma star_eta_pow {η : ℂ} (hη : η = 1 ∨ η = -1) (m : ℕ) :
    star (η ^ m) = η ^ m := by
  rcases hη with rfl | rfl <;> simp

lemma eta_pow_even {η : ℂ} (hη : η = 1 ∨ η = -1) {m : ℕ} (hm : Even m) :
    η ^ m = 1 := by
  rcases hm with ⟨k, rfl⟩
  rw [show k + k = 2 * k by omega, pow_mul, eta_sq_eq_one hη, one_pow]

lemma eta_pow_eq_of_modeq {η : ℂ} (hη : η = 1 ∨ η = -1) {a b : ℕ}
    (h : a % 2 = b % 2) : η ^ a = η ^ b := by
  have ha : a = 2 * (a / 2) + a % 2 := (Nat.div_add_mod a 2).symm
  have hb : b = 2 * (b / 2) + b % 2 := (Nat.div_add_mod b 2).symm
  rw [ha, hb, pow_add, pow_add, pow_mul, pow_mul, eta_sq_eq_one hη,
      one_pow, one_pow, one_mul, one_mul, h]

lemma eta_pow_permInversions_eq_sign {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ((-1 : ℂ) ^ permInversions σ) = ((Equiv.Perm.sign σ : ℤ) : ℂ) := by
  have h := congrArg (Int.cast (R := ℂ)) (zpow_neg_one_permInversions σ)
  simpa using h

lemma eta_pow_permInversions_mul {η : ℂ} (hη : η = 1 ∨ η = -1)
    {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    η ^ permInversions (σ * τ) = η ^ permInversions σ * η ^ permInversions τ := by
  rcases hη with rfl | rfl
  · simp
  · rw [eta_pow_permInversions_eq_sign, eta_pow_permInversions_eq_sign,
        eta_pow_permInversions_eq_sign, map_mul]
    push_cast
    rfl

lemma eta_pow_permInversions_inv {η : ℂ} (hη : η = 1 ∨ η = -1)
    {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    η ^ permInversions σ⁻¹ = η ^ permInversions σ := by
  have h1 := eta_pow_permInversions_mul hη σ σ⁻¹
  rw [mul_inv_cancel, permInversions_one, pow_zero] at h1
  have h2 : η ^ permInversions σ * η ^ permInversions σ = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, eta_sq_eq_one hη, one_pow]
  exact mul_left_cancel₀ (pow_ne_zero _ (eta_ne_zero hη)) (h1.symm.trans h2.symm)

@[ext]
structure ChordPairing (n : ℕ) where
  mate : Equiv.Perm (Fin n)
  involutive : Function.Involutive mate
  ne_self : ∀ i : Fin n, mate i ≠ i

namespace ChordPairing

def toSubtypeEquiv (n : ℕ) :
    ChordPairing n ≃
      { m : Equiv.Perm (Fin n) // (∀ i : Fin n, m (m i) = i) ∧ (∀ i : Fin n, m i ≠ i) } where
  toFun P := ⟨P.mate, ⟨P.involutive, P.ne_self⟩⟩
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv P := by cases P; rfl
  right_inv x := by cases x; rfl

instance instDecidableEq (n : ℕ) : DecidableEq (ChordPairing n) :=
  Equiv.decidableEq (toSubtypeEquiv n)

instance instFintype (n : ℕ) : Fintype (ChordPairing n) :=
  Fintype.ofEquiv _ (toSubtypeEquiv n).symm

@[simp]
lemma mate_mate {n : ℕ} (P : ChordPairing n) (i : Fin n) :
    P.mate (P.mate i) = i :=
  P.involutive i

@[simp]
lemma mate_symm {n : ℕ} (P : ChordPairing n) :
    P.mate.symm = P.mate := by
  apply Equiv.ext
  intro i
  exact P.mate.symm_apply_eq.mpr (P.mate_mate i).symm

abbrev Chord {n : ℕ} (P : ChordPairing n) : Type :=
  { i : Fin n // i < P.mate i }

lemma lt_or_gt_mate {n : ℕ} (P : ChordPairing n) (i : Fin n) :
    i < P.mate i ∨ P.mate i < i :=
  lt_or_gt_of_ne (P.ne_self i).symm

def chordSlotMap {n : ℕ} (P : ChordPairing n) : P.Chord × Fin 2 → Fin n
  | (c, 0) => c.1
  | (c, 1) => P.mate c.1

def chordSlotInv {n : ℕ} (P : ChordPairing n) (i : Fin n) : P.Chord × Fin 2 :=
  if h : i < P.mate i then
    (⟨i, h⟩, 0)
  else
    (⟨P.mate i, by
      have hgt : P.mate i < i := (P.lt_or_gt_mate i).resolve_left h
      simpa [P.mate_mate] using hgt⟩, 1)

def chordSlotEquiv {n : ℕ} (P : ChordPairing n) : P.Chord × Fin 2 ≃ Fin n where
  toFun := P.chordSlotMap
  invFun := P.chordSlotInv
  left_inv := by
    rintro ⟨⟨i, hi⟩, s⟩
    fin_cases s
    · dsimp [chordSlotMap, chordSlotInv]
      rw [dif_pos hi]
    · dsimp [chordSlotMap, chordSlotInv]
      have hnot : ¬ P.mate i < P.mate (P.mate i) := by
        rw [P.mate_mate]
        exact not_lt_of_gt hi
      rw [dif_neg hnot]
      exact Prod.ext (Subtype.ext (P.mate_mate i)) rfl
  right_inv := by
    intro i
    dsimp [chordSlotInv]
    split_ifs with hi
    · rfl
    · dsimp [chordSlotMap]
      exact P.mate_mate i

@[simp]
lemma chordSlotEquiv_zero {n : ℕ} (P : ChordPairing n) (c : P.Chord) :
    P.chordSlotEquiv (c, 0) = c.1 := rfl

@[simp]
lemma chordSlotEquiv_one {n : ℕ} (P : ChordPairing n) (c : P.Chord) :
    P.chordSlotEquiv (c, 1) = P.mate c.1 := rfl

lemma two_mul_card_chord {n : ℕ} (P : ChordPairing n) :
    2 * Fintype.card P.Chord = n := by
  have h := Fintype.card_congr P.chordSlotEquiv
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h
  omega

lemma even_of_nonempty {n : ℕ} (P : ChordPairing n) : Even n :=
  ⟨Fintype.card P.Chord, by have := P.two_mul_card_chord; omega⟩

lemma isEmpty_of_odd {n : ℕ} (hodd : Odd n) : IsEmpty (ChordPairing n) :=
  ⟨fun P => (Nat.not_even_iff_odd.mpr hodd) P.even_of_nonempty⟩

def zeroPairing : ChordPairing 0 where
  mate := 1
  involutive i := Fin.elim0 i
  ne_self i := Fin.elim0 i

instance instUniqueZero : Unique (ChordPairing 0) where
  default := zeroPairing
  uniq P := by
    apply ChordPairing.ext
    apply Equiv.ext
    intro i
    exact Fin.elim0 i

def twoPairing : ChordPairing 2 where
  mate := Equiv.swap 0 1
  involutive i := Equiv.swap_apply_self 0 1 i
  ne_self i := by fin_cases i <;> decide

instance instUniqueTwo : Unique (ChordPairing 2) where
  default := twoPairing
  uniq P := by
    apply ChordPairing.ext
    apply Equiv.ext
    intro i
    fin_cases i
    · have hne := P.ne_self 0
      rcases Fin.exists_fin_two.mp ⟨P.mate 0, rfl⟩ with h0 | h1
      · exact False.elim (hne h0)
      · exact h1
    · have hne := P.ne_self 1
      rcases Fin.exists_fin_two.mp ⟨P.mate 1, rfl⟩ with h0 | h1
      · exact h0
      · exact False.elim (hne h1)

lemma unique_twoPairing_chord :
    (Finset.univ : Finset twoPairing.Chord) = {⟨0, by decide⟩} := by
  ext ⟨i, hi⟩
  simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
  apply Subtype.ext
  fin_cases i
  · rfl
  · exfalso
    revert hi
    decide

lemma prod_univ_eq_prod_chord {M : Type*} [CommMonoid M] {n : ℕ}
    (P : ChordPairing n) (f : Fin n → M) :
    (∏ i : Fin n, f i) = ∏ c : P.Chord, f c.1 * f (P.mate c.1) := by
  rw [← P.chordSlotEquiv.prod_comp, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl (fun c _ => ?_)
  rw [Fin.prod_univ_two]
  rfl

lemma sum_univ_eq_sum_chord {M : Type*} [AddCommMonoid M] {n : ℕ}
    (P : ChordPairing n) (f : Fin n → M) :
    (∑ i : Fin n, f i) = ∑ c : P.Chord, (f c.1 + f (P.mate c.1)) := by
  rw [← P.chordSlotEquiv.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Fin.sum_univ_two]
  rfl

def funFromChord {ι : Type*} {n : ℕ} (P : ChordPairing n) :
    (P.Chord → Fin 2 → ι) ≃ (Fin n → ι) :=
  (Equiv.curry P.Chord (Fin 2) ι).symm.trans (P.chordSlotEquiv.arrowCongr (Equiv.refl ι))

@[simp]
lemma funFromChord_apply_fst {ι : Type*} {n : ℕ} (P : ChordPairing n)
    (g : P.Chord → Fin 2 → ι) (c : P.Chord) :
    P.funFromChord g c.1 = g c 0 := by
  have hsym : P.chordSlotEquiv.symm c.1 = (c, 0) :=
    P.chordSlotEquiv.symm_apply_eq.mpr rfl
  change g (P.chordSlotEquiv.symm c.1).1 (P.chordSlotEquiv.symm c.1).2 = g c 0
  rw [hsym]

@[simp]
lemma funFromChord_apply_mate {ι : Type*} {n : ℕ} (P : ChordPairing n)
    (g : P.Chord → Fin 2 → ι) (c : P.Chord) :
    P.funFromChord g (P.mate c.1) = g c 1 := by
  have hsym : P.chordSlotEquiv.symm (P.mate c.1) = (c, 1) :=
    P.chordSlotEquiv.symm_apply_eq.mpr rfl
  change g (P.chordSlotEquiv.symm (P.mate c.1)).1
    (P.chordSlotEquiv.symm (P.mate c.1)).2 = g c 1
  rw [hsym]

lemma vecTwo_funFromChord {ι : Type*} {n : ℕ} (P : ChordPairing n)
    (g : P.Chord → Fin 2 → ι) (c : P.Chord) :
    ![P.funFromChord g c.1, P.funFromChord g (P.mate c.1)] = g c := by
  ext s
  fin_cases s
  · exact P.funFromChord_apply_fst g c
  · exact P.funFromChord_apply_mate g c

lemma sum_prod_chord_factor {ι : Type*} [Fintype ι] {n : ℕ}
    (P : ChordPairing n) (M : Fin n → ι → ℂ) (F : P.Chord → (Fin 2 → ι) → ℂ) :
    (∑ β : Fin n → ι,
      (∏ i : Fin n, M i (β i)) * ∏ c : P.Chord, F c ![β c.1, β (P.mate c.1)]) =
      ∏ c : P.Chord,
        ∑ γ : Fin 2 → ι, (M c.1 (γ 0) * M (P.mate c.1) (γ 1)) * F c γ := by
  rw [← P.funFromChord.sum_comp]
  have h_term : ∀ g : P.Chord → Fin 2 → ι,
      (∏ i : Fin n, M i (P.funFromChord g i)) *
        (∏ c : P.Chord, F c ![P.funFromChord g c.1, P.funFromChord g (P.mate c.1)]) =
      ∏ c : P.Chord, (M c.1 (g c 0) * M (P.mate c.1) (g c 1)) * F c (g c) := by
    intro g
    rw [P.prod_univ_eq_prod_chord (fun i => M i (P.funFromChord g i)),
        ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun c _ => ?_)
    rw [P.vecTwo_funFromChord g c, P.funFromChord_apply_fst, P.funFromChord_apply_mate]
  simp_rw [h_term]
  exact (Fintype.prod_sum (fun c γ => (M c.1 (γ 0) * M (P.mate c.1) (γ 1)) * F c γ)).symm

def cross {n : ℕ} (P : ChordPairing n) : ℕ :=
  (Finset.univ.filter (fun ij : Fin n × Fin n =>
    ij.1 < ij.2 ∧ ij.2 < P.mate ij.1 ∧ P.mate ij.1 < P.mate ij.2)).card

@[simp]
lemma cross_zero : zeroPairing.cross = 0 := by
  rfl

@[simp]
lemma cross_two : twoPairing.cross = 0 := by
  decide

def rev {n : ℕ} (P : ChordPairing n) : ChordPairing n where
  mate := (finRevPerm n).trans (P.mate.trans (finRevPerm n))
  involutive i := by
    change Fin.rev (P.mate (Fin.rev (Fin.rev (P.mate (Fin.rev i))))) = i
    rw [Fin.rev_rev, P.mate_mate, Fin.rev_rev]
  ne_self i := by
    change Fin.rev (P.mate (Fin.rev i)) ≠ i
    intro h
    have h' := congrArg Fin.rev h
    rw [Fin.rev_rev] at h'
    exact P.ne_self (Fin.rev i) h'

@[simp]
lemma rev_mate_apply {n : ℕ} (P : ChordPairing n) (i : Fin n) :
    P.rev.mate i = Fin.rev (P.mate (Fin.rev i)) := rfl

@[simp]
lemma rev_rev {n : ℕ} (P : ChordPairing n) : P.rev.rev = P := by
  apply ChordPairing.ext
  apply Equiv.ext
  intro i
  change Fin.rev (Fin.rev (P.mate (Fin.rev (Fin.rev i)))) = P.mate i
  rw [Fin.rev_rev, Fin.rev_rev]

def revEquiv (n : ℕ) : ChordPairing n ≃ ChordPairing n where
  toFun := rev
  invFun := rev
  left_inv := rev_rev
  right_inv := rev_rev

def revChordEquiv {n : ℕ} (P : ChordPairing n) : P.Chord ≃ P.rev.Chord where
  toFun c := ⟨Fin.rev (P.mate c.1), by
    change Fin.rev (P.mate c.1) < Fin.rev (P.mate (Fin.rev (Fin.rev (P.mate c.1))))
    rw [Fin.rev_rev, P.mate_mate, Fin.rev_lt_rev]
    exact c.2⟩
  invFun c' := ⟨Fin.rev (P.rev.mate c'.1), by
    have hc' : c'.1 < Fin.rev (P.mate (Fin.rev c'.1)) := c'.2
    have h_eq : P.mate (Fin.rev (P.rev.mate c'.1)) = Fin.rev c'.1 := by
      change P.mate (Fin.rev (Fin.rev (P.mate (Fin.rev c'.1)))) = Fin.rev c'.1
      rw [Fin.rev_rev, P.mate_mate]
    rw [h_eq]
    change Fin.rev (Fin.rev (P.mate (Fin.rev c'.1))) < Fin.rev c'.1
    rw [Fin.rev_lt_rev]
    exact hc'⟩
  left_inv c := by
    apply Subtype.ext
    simp only [rev_mate_apply, Fin.rev_rev, P.mate_mate]
  right_inv c' := by
    apply Subtype.ext
    simp only [rev_mate_apply, Fin.rev_rev, P.mate_mate]

@[simp]
lemma cross_rev {n : ℕ} (P : ChordPairing n) : P.rev.cross = P.cross := by
  dsimp [cross]
  apply Finset.card_bij (fun (uv : Fin n × Fin n) _ =>
    (Fin.rev (P.rev.mate uv.2), Fin.rev (P.rev.mate uv.1)))
  · intro ⟨u, v⟩ huv
    rw [Finset.mem_filter] at huv ⊢
    rcases huv with ⟨_, huv_lt, hv_lt, hmu_lt⟩
    simp only [rev_mate_apply, Fin.rev_rev, P.mate_mate, Fin.rev_lt_rev] at huv_lt hv_lt hmu_lt ⊢
    exact ⟨Finset.mem_univ _, hmu_lt, Fin.rev_lt_rev.mp (by simpa using hv_lt), huv_lt⟩
  · intro ⟨u1, v1⟩ _ ⟨u2, v2⟩ _ h_eq
    dsimp only at h_eq
    rcases Prod.mk.inj h_eq with ⟨h1, h2⟩
    have hv : v1 = v2 := P.rev.mate.injective (Fin.rev_injective h1)
    have hu : u1 = u2 := P.rev.mate.injective (Fin.rev_injective h2)
    exact Prod.ext hu hv
  · intro ⟨i, j⟩ hij
    rw [Finset.mem_filter] at hij
    rcases hij with ⟨_, hij_lt, hj_lt, hmi_lt⟩
    refine ⟨(Fin.rev (P.mate j), Fin.rev (P.mate i)), ?_, ?_⟩
    · rw [Finset.mem_filter]
      simp only [Fin.rev_rev, P.mate_mate, Fin.rev_lt_rev]
      exact ⟨Finset.mem_univ _, hmi_lt, hj_lt, hij_lt⟩
    · simp only [rev_mate_apply, Fin.rev_rev, P.mate_mate]

lemma card_chord_mod_two_eq_choose_two {n : ℕ} (P : ChordPairing n) :
    Fintype.card P.Chord % 2 = (n * (n - 1) / 2) % 2 := by
  let k := Fintype.card P.Chord
  have hn : n = 2 * k := P.two_mul_card_chord.symm
  change k % 2 = (n * (n - 1) / 2) % 2
  rw [hn]
  rcases k with _ | m
  · simp
  · have h_mul : 2 * (m + 1) * (2 * (m + 1) - 1) / 2 = 2 * ((m + 1) * m) + (m + 1) := by
      have h1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
      have h2 : (m + 1) * (2 * m + 1) = 2 * ((m + 1) * m) + (m + 1) := by ring
      rw [h1, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by positivity), h2]
    rw [h_mul, Nat.mul_add_mod]

theorem eta_pow_card_chord_mul_cross {η : ℂ} (hη : η = 1 ∨ η = -1)
    {n : ℕ} (P : ChordPairing n) :
    η ^ Fintype.card P.Chord * η ^ P.cross =
      η ^ (n * (n - 1) / 2) * η ^ P.rev.cross := by
  rw [P.cross_rev, eta_pow_eq_of_modeq hη P.card_chord_mod_two_eq_choose_two]

end ChordPairing

def concatSlotEquiv (j k : ℕ) : Fin j ⊕ Fin k ≃ Fin (j + k) :=
  (Equiv.sumCongr (finRevPerm j) (Equiv.refl (Fin k))).trans finSumFinEquiv

lemma concatSlotEquiv_inl (j k : ℕ) (i : Fin j) :
    concatSlotEquiv j k (Sum.inl i) = Fin.castAdd k (Fin.rev i) := rfl

lemma concatSlotEquiv_inr (j k : ℕ) (t : Fin k) :
    concatSlotEquiv j k (Sum.inr t) = Fin.natAdd j t := rfl

@[simp]
lemma concatSlotEquiv_inl_lt_inl {j k : ℕ} (i₁ i₂ : Fin j) :
    concatSlotEquiv j k (Sum.inl i₁) < concatSlotEquiv j k (Sum.inl i₂) ↔ i₂ < i₁ := by
  change Fin.castAdd k (Fin.rev i₁) < Fin.castAdd k (Fin.rev i₂) ↔ i₂ < i₁
  have h1 :
      Fin.castAdd k (Fin.rev i₁) < Fin.castAdd k (Fin.rev i₂) ↔
        Fin.rev i₁ < Fin.rev i₂ := by
    simp only [Fin.lt_def, Fin.val_castAdd]
  rw [h1, Fin.rev_lt_rev]

@[simp]
lemma concatSlotEquiv_inl_lt_inr {j k : ℕ} (i : Fin j) (t : Fin k) :
    concatSlotEquiv j k (Sum.inl i) < concatSlotEquiv j k (Sum.inr t) := by
  change Fin.castAdd k (Fin.rev i) < Fin.natAdd j t
  have hi : (Fin.rev i).val < j := (Fin.rev i).isLt
  simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
  omega

@[simp]
lemma not_concatSlotEquiv_inr_lt_inl {j k : ℕ} (t : Fin k) (i : Fin j) :
    ¬ concatSlotEquiv j k (Sum.inr t) < concatSlotEquiv j k (Sum.inl i) :=
  not_lt_of_gt (concatSlotEquiv_inl_lt_inr i t)

@[simp]
lemma concatSlotEquiv_inr_lt_inr {j k : ℕ} (t₁ t₂ : Fin k) :
    concatSlotEquiv j k (Sum.inr t₁) < concatSlotEquiv j k (Sum.inr t₂) ↔ t₁ < t₂ := by
  change Fin.natAdd j t₁ < Fin.natAdd j t₂ ↔ t₁ < t₂
  simp only [Fin.lt_def, Fin.val_natAdd]
  omega

@[ext]
structure PartialPairing (n r : ℕ) where
  unpaired : Fin r → Fin n
  strictMono_unpaired : StrictMono unpaired
  mate : Equiv.Perm (Fin n)
  involutive : Function.Involutive mate
  fixed_iff : ∀ i : Fin n, mate i = i ↔ ∃ a : Fin r, unpaired a = i

namespace PartialPairing

def toSubtypeEquiv (n r : ℕ) :
    PartialPairing n r ≃
      { um : (Fin r → Fin n) × Equiv.Perm (Fin n) //
        (∀ a b : Fin r, a < b → um.1 a < um.1 b) ∧
        (∀ i : Fin n, um.2 (um.2 i) = i) ∧
        (∀ i : Fin n, um.2 i = i ↔ ∃ a : Fin r, um.1 a = i) } where
  toFun L := ⟨(L.unpaired, L.mate), ⟨L.strictMono_unpaired, L.involutive, L.fixed_iff⟩⟩
  invFun x := ⟨x.1.1, x.2.1, x.1.2, x.2.2.1, x.2.2.2⟩
  left_inv L := by cases L; rfl
  right_inv x := by rcases x with ⟨⟨_, _⟩, _⟩; rfl

instance instDecidableEq (n r : ℕ) : DecidableEq (PartialPairing n r) :=
  Equiv.decidableEq (toSubtypeEquiv n r)

instance instFintype (n r : ℕ) : Fintype (PartialPairing n r) :=
  Fintype.ofEquiv _ (toSubtypeEquiv n r).symm

@[simp]
lemma mate_mate {n r : ℕ} (L : PartialPairing n r) (i : Fin n) :
    L.mate (L.mate i) = i :=
  L.involutive i

@[simp]
lemma mate_unpaired {n r : ℕ} (L : PartialPairing n r) (a : Fin r) :
    L.mate (L.unpaired a) = L.unpaired a :=
  (L.fixed_iff (L.unpaired a)).mpr ⟨a, rfl⟩

lemma unpaired_injective {n r : ℕ} (L : PartialPairing n r) :
    Function.Injective L.unpaired :=
  L.strictMono_unpaired.injective

lemma ext_mate {n r : ℕ} {M₁ M₂ : PartialPairing n r} (hm : M₁.mate = M₂.mate) :
    M₁ = M₂ := by
  refine PartialPairing.ext ?_ hm
  refine (StrictMono.range_inj M₁.strictMono_unpaired M₂.strictMono_unpaired).mp ?_
  ext i
  simp only [Set.mem_range, ← M₁.fixed_iff, ← M₂.fixed_iff, hm]

lemma le_of_nonempty {n r : ℕ} (L : PartialPairing n r) : r ≤ n := by
  have h := Fintype.card_le_of_injective L.unpaired L.unpaired_injective
  simpa using h

def unpairedIdx {n r : ℕ} (L : PartialPairing n r) (i : Fin n)
    (h : L.mate i = i) : Fin r :=
  Fintype.choose (fun a : Fin r => L.unpaired a = i) (by
    rcases (L.fixed_iff i).mp h with ⟨a, ha⟩
    exact ⟨a, ha, fun b hb => L.unpaired_injective (hb.trans ha.symm)⟩)

@[simp]
lemma unpaired_unpairedIdx {n r : ℕ} (L : PartialPairing n r) (i : Fin n)
    (h : L.mate i = i) :
    L.unpaired (L.unpairedIdx i h) = i :=
  Fintype.choose_spec (fun a : Fin r => L.unpaired a = i) _

@[simp]
lemma unpairedIdx_unpaired {n r : ℕ} (L : PartialPairing n r) (a : Fin r)
    (h : L.mate (L.unpaired a) = L.unpaired a := L.mate_unpaired a) :
    L.unpairedIdx (L.unpaired a) h = a :=
  L.unpaired_injective (L.unpaired_unpairedIdx (L.unpaired a) h)

abbrev InternalChord {n r : ℕ} (L : PartialPairing n r) : Type :=
  { i : Fin n // i < L.mate i }

lemma mate_ne_self_of_internalChord {n r : ℕ} (L : PartialPairing n r)
    (c : L.InternalChord) : L.mate c.1 ≠ c.1 :=
  (ne_of_lt c.2).symm

lemma mate_mate_ne_of_internalChord {n r : ℕ} (L : PartialPairing n r)
    (c : L.InternalChord) : L.mate (L.mate c.1) ≠ L.mate c.1 := by
  rw [L.mate_mate]
  exact ne_of_lt c.2

def partialSlotMap {n r : ℕ} (L : PartialPairing n r) :
    Fin r ⊕ (L.InternalChord × Fin 2) → Fin n
  | Sum.inl a => L.unpaired a
  | Sum.inr (c, 0) => c.1
  | Sum.inr (c, 1) => L.mate c.1

def partialSlotInv {n r : ℕ} (L : PartialPairing n r) (i : Fin n) :
    Fin r ⊕ (L.InternalChord × Fin 2) :=
  if h : L.mate i = i then
    Sum.inl (L.unpairedIdx i h)
  else if hlt : i < L.mate i then
    Sum.inr (⟨i, hlt⟩, 0)
  else
    Sum.inr (⟨L.mate i, by
      have hgt : L.mate i < i := (lt_or_gt_of_ne (Ne.symm h)).resolve_left hlt
      simpa [L.mate_mate] using hgt⟩, 1)

def partialSlotEquiv {n r : ℕ} (L : PartialPairing n r) :
    Fin r ⊕ (L.InternalChord × Fin 2) ≃ Fin n where
  toFun := L.partialSlotMap
  invFun := L.partialSlotInv
  left_inv := by
    rintro (a | ⟨c, s⟩)
    · dsimp [partialSlotMap, partialSlotInv]
      rw [dif_pos (L.mate_unpaired a), L.unpairedIdx_unpaired]
    · fin_cases s
      · dsimp [partialSlotMap, partialSlotInv]
        rw [dif_neg (L.mate_ne_self_of_internalChord c), dif_pos c.2]
      · dsimp [partialSlotMap, partialSlotInv]
        have hnot : ¬ L.mate c.1 < L.mate (L.mate c.1) := by
          rw [L.mate_mate]
          exact not_lt_of_gt c.2
        rw [dif_neg (L.mate_mate_ne_of_internalChord c), dif_neg hnot]
        exact congrArg Sum.inr (Prod.ext (Subtype.ext (L.mate_mate c.1)) rfl)
  right_inv := by
    intro i
    dsimp [partialSlotInv]
    split_ifs with h hlt
    · exact L.unpaired_unpairedIdx i h
    · rfl
    · dsimp [partialSlotMap]
      exact L.mate_mate i

lemma prod_univ_eq_prod_partial {M : Type*} [CommMonoid M] {n r : ℕ}
    (L : PartialPairing n r) (f : Fin n → M) :
    (∏ i : Fin n, f i) =
      (∏ a : Fin r, f (L.unpaired a)) *
        ∏ c : L.InternalChord, f c.1 * f (L.mate c.1) := by
  rw [← L.partialSlotEquiv.prod_comp, Fintype.prod_sum_type, Fintype.prod_prod_type]
  congr 1
  refine Finset.prod_congr rfl (fun c _ => ?_)
  rw [Fin.prod_univ_two]
  rfl

def funFromPartial {ι : Type*} {n r : ℕ} (L : PartialPairing n r) :
    ((Fin r → ι) × (L.InternalChord → Fin 2 → ι)) ≃ (Fin n → ι) :=
  ((Equiv.refl (Fin r → ι)).prodCongr (Equiv.curry L.InternalChord (Fin 2) ι).symm).trans
    ((Equiv.sumArrowEquivProdArrow (Fin r) (L.InternalChord × Fin 2) ι).symm.trans
      (L.partialSlotEquiv.arrowCongr (Equiv.refl ι)))

@[simp]
lemma funFromPartial_apply_unpaired {ι : Type*} {n r : ℕ} (L : PartialPairing n r)
    (δ : Fin r → ι) (g : L.InternalChord → Fin 2 → ι) (a : Fin r) :
    L.funFromPartial (δ, g) (L.unpaired a) = δ a := by
  have hsym : L.partialSlotEquiv.symm (L.unpaired a) = Sum.inl a :=
    L.partialSlotEquiv.symm_apply_eq.mpr rfl
  change Sum.elim δ (Function.uncurry g) (L.partialSlotEquiv.symm (L.unpaired a)) = δ a
  rw [hsym]
  rfl

@[simp]
lemma funFromPartial_apply_fst {ι : Type*} {n r : ℕ} (L : PartialPairing n r)
    (δ : Fin r → ι) (g : L.InternalChord → Fin 2 → ι) (c : L.InternalChord) :
    L.funFromPartial (δ, g) c.1 = g c 0 := by
  have hsym : L.partialSlotEquiv.symm c.1 = Sum.inr (c, 0) :=
    L.partialSlotEquiv.symm_apply_eq.mpr rfl
  change Sum.elim δ (Function.uncurry g) (L.partialSlotEquiv.symm c.1) = g c 0
  rw [hsym]
  rfl

@[simp]
lemma funFromPartial_apply_mate {ι : Type*} {n r : ℕ} (L : PartialPairing n r)
    (δ : Fin r → ι) (g : L.InternalChord → Fin 2 → ι) (c : L.InternalChord) :
    L.funFromPartial (δ, g) (L.mate c.1) = g c 1 := by
  have hsym : L.partialSlotEquiv.symm (L.mate c.1) = Sum.inr (c, 1) :=
    L.partialSlotEquiv.symm_apply_eq.mpr rfl
  change Sum.elim δ (Function.uncurry g) (L.partialSlotEquiv.symm (L.mate c.1)) = g c 1
  rw [hsym]
  rfl

lemma vecTwo_funFromPartial {ι : Type*} {n r : ℕ} (L : PartialPairing n r)
    (δ : Fin r → ι) (g : L.InternalChord → Fin 2 → ι) (c : L.InternalChord) :
    ![L.funFromPartial (δ, g) c.1, L.funFromPartial (δ, g) (L.mate c.1)] = g c := by
  ext s
  fin_cases s
  · exact L.funFromPartial_apply_fst δ g c
  · exact L.funFromPartial_apply_mate δ g c

lemma sum_prod_partial_factor {ι : Type*} [Fintype ι] {n r : ℕ}
    (L : PartialPairing n r) (M : Fin n → ι → ℂ)
    (G : (Fin r → ι) → ℂ) (F : L.InternalChord → (Fin 2 → ι) → ℂ) :
    (∑ β : Fin n → ι,
      (∏ i : Fin n, M i (β i)) * G (fun a => β (L.unpaired a)) *
        ∏ c : L.InternalChord, F c ![β c.1, β (L.mate c.1)]) =
      (∑ δ : Fin r → ι, (∏ a : Fin r, M (L.unpaired a) (δ a)) * G δ) *
        ∏ c : L.InternalChord,
          ∑ γ : Fin 2 → ι, (M c.1 (γ 0) * M (L.mate c.1) (γ 1)) * F c γ := by
  rw [← L.funFromPartial.sum_comp, Fintype.sum_prod_type]
  have h_inner : ∀ (δ : Fin r → ι) (g : L.InternalChord → Fin 2 → ι),
      (∏ i : Fin n, M i (L.funFromPartial (δ, g) i)) *
        G (fun a => L.funFromPartial (δ, g) (L.unpaired a)) *
        (∏ c : L.InternalChord,
          F c ![L.funFromPartial (δ, g) c.1, L.funFromPartial (δ, g) (L.mate c.1)]) =
      ((∏ a : Fin r, M (L.unpaired a) (δ a)) * G δ) *
        ∏ c : L.InternalChord, (M c.1 (g c 0) * M (L.mate c.1) (g c 1)) * F c (g c) := by
    intro δ g
    rw [L.prod_univ_eq_prod_partial (fun i => M i (L.funFromPartial (δ, g) i))]
    have hδ1 : (∏ a : Fin r, M (L.unpaired a) (L.funFromPartial (δ, g) (L.unpaired a))) =
        ∏ a : Fin r, M (L.unpaired a) (δ a) := by
      refine Finset.prod_congr rfl (fun a _ => ?_)
      rw [L.funFromPartial_apply_unpaired]
    have hδ2 : (fun a : Fin r => L.funFromPartial (δ, g) (L.unpaired a)) = δ := by
      ext a
      exact L.funFromPartial_apply_unpaired δ g a
    have hg :
        (∏ c : L.InternalChord,
          M c.1 (L.funFromPartial (δ, g) c.1) *
            M (L.mate c.1) (L.funFromPartial (δ, g) (L.mate c.1))) *
        (∏ c : L.InternalChord,
          F c ![L.funFromPartial (δ, g) c.1, L.funFromPartial (δ, g) (L.mate c.1)]) =
        ∏ c : L.InternalChord,
          (M c.1 (g c 0) * M (L.mate c.1) (g c 1)) * F c (g c) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun c _ => ?_)
      rw [L.vecTwo_funFromPartial, L.funFromPartial_apply_fst, L.funFromPartial_apply_mate]
    rw [hδ1, hδ2]
    calc ((∏ a : Fin r, M (L.unpaired a) (δ a)) *
          ∏ c : L.InternalChord,
            M c.1 (L.funFromPartial (δ, g) c.1) *
              M (L.mate c.1) (L.funFromPartial (δ, g) (L.mate c.1))) *
          G δ *
          (∏ c : L.InternalChord,
            F c ![L.funFromPartial (δ, g) c.1, L.funFromPartial (δ, g) (L.mate c.1)])
        = ((∏ a : Fin r, M (L.unpaired a) (δ a)) * G δ) *
          ((∏ c : L.InternalChord,
            M c.1 (L.funFromPartial (δ, g) c.1) *
              M (L.mate c.1) (L.funFromPartial (δ, g) (L.mate c.1))) *
            ∏ c : L.InternalChord,
              F c ![L.funFromPartial (δ, g) c.1, L.funFromPartial (δ, g) (L.mate c.1)]) := by ring
      _ = ((∏ a : Fin r, M (L.unpaired a) (δ a)) * G δ) *
          ∏ c : L.InternalChord, (M c.1 (g c 0) * M (L.mate c.1) (g c 1)) * F c (g c) := by
          rw [hg]
  simp_rw [h_inner, ← Finset.mul_sum, ← Finset.sum_mul]
  congr 1
  exact (Fintype.prod_sum (fun c γ => (M c.1 (γ 0) * M (L.mate c.1) (γ 1)) * F c γ)).symm

def internalCross {n r : ℕ} (L : PartialPairing n r) : ℕ :=
  (Finset.univ.filter (fun ij : Fin n × Fin n =>
    ij.1 < ij.2 ∧ ij.2 < L.mate ij.1 ∧ L.mate ij.1 < L.mate ij.2)).card

def openCross {n r : ℕ} (L : PartialPairing n r) : ℕ :=
  (Finset.univ.filter (fun ca : Fin n × Fin r =>
    ca.1 < L.unpaired ca.2 ∧ L.unpaired ca.2 < L.mate ca.1)).card

def partialCross {n r : ℕ} (L : PartialPairing n r) : ℕ :=
  L.internalCross + L.openCross

def toChordPairing {n : ℕ} (L : PartialPairing n 0) : ChordPairing n where
  mate := L.mate
  involutive := L.involutive
  ne_self i h := by
    rcases (L.fixed_iff i).mp h with ⟨a, _⟩
    exact Fin.elim0 a

def ofChordPairing {n : ℕ} (P : ChordPairing n) : PartialPairing n 0 where
  unpaired := Fin.elim0
  strictMono_unpaired a := Fin.elim0 a
  mate := P.mate
  involutive := P.involutive
  fixed_iff i := ⟨fun h => False.elim (P.ne_self i h), fun ⟨a, _⟩ => Fin.elim0 a⟩

def zeroUnpairedEquiv (n : ℕ) : PartialPairing n 0 ≃ ChordPairing n where
  toFun := toChordPairing
  invFun := ofChordPairing
  left_inv L := by
    apply PartialPairing.ext
    · ext a; exact Fin.elim0 a
    · rfl
  right_inv P := by cases P; rfl

@[simp]
lemma partialCross_ofChordPairing {n : ℕ} (P : ChordPairing n) :
    (ofChordPairing P).partialCross = P.cross := by
  have hopen : (ofChordPairing P).openCross = 0 := by
    dsimp [openCross]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro ⟨_, a⟩
    exact Fin.elim0 a
  dsimp [partialCross]
  rw [hopen, add_zero]
  rfl

def concatSumFun {j k r : ℕ} (L : PartialPairing j r) (R : PartialPairing k r)
    (σ : Equiv.Perm (Fin r)) : Fin j ⊕ Fin k → Fin j ⊕ Fin k
  | Sum.inl i =>
      if h : L.mate i = i then
        Sum.inr (R.unpaired (σ (L.unpairedIdx i h)))
      else
        Sum.inl (L.mate i)
  | Sum.inr t =>
      if h : R.mate t = t then
        Sum.inl (L.unpaired (σ.symm (R.unpairedIdx t h)))
      else
        Sum.inr (R.mate t)

lemma concatSumFun_involutive {j k r : ℕ} (L : PartialPairing j r) (R : PartialPairing k r)
    (σ : Equiv.Perm (Fin r)) :
    Function.Involutive (concatSumFun L R σ) := by
  rintro (i | t)
  · dsimp [concatSumFun]
    split_ifs with h
    · dsimp [concatSumFun]
      rw [dif_pos (R.mate_unpaired _), R.unpairedIdx_unpaired, σ.symm_apply_apply,
          L.unpaired_unpairedIdx]
    · dsimp [concatSumFun]
      have h2 : L.mate (L.mate i) ≠ L.mate i := by
        rw [L.mate_mate]
        exact Ne.symm h
      rw [dif_neg h2, L.mate_mate]
  · dsimp [concatSumFun]
    split_ifs with h
    · dsimp [concatSumFun]
      rw [dif_pos (L.mate_unpaired _), L.unpairedIdx_unpaired, σ.apply_symm_apply,
          R.unpaired_unpairedIdx]
    · dsimp [concatSumFun]
      have h2 : R.mate (R.mate t) ≠ R.mate t := by
        rw [R.mate_mate]
        exact Ne.symm h
      rw [dif_neg h2, R.mate_mate]

lemma concatSumFun_ne_self {j k r : ℕ} (L : PartialPairing j r) (R : PartialPairing k r)
    (σ : Equiv.Perm (Fin r)) (x : Fin j ⊕ Fin k) :
    concatSumFun L R σ x ≠ x := by
  rcases x with i | t
  · dsimp [concatSumFun]
    split_ifs with h
    · simp
    · simpa using h
  · dsimp [concatSumFun]
    split_ifs with h
    · simp
    · simpa using h

def concatSumPerm {j k r : ℕ} (L : PartialPairing j r) (R : PartialPairing k r)
    (σ : Equiv.Perm (Fin r)) : Equiv.Perm (Fin j ⊕ Fin k) where
  toFun := concatSumFun L R σ
  invFun := concatSumFun L R σ
  left_inv := concatSumFun_involutive L R σ
  right_inv := concatSumFun_involutive L R σ

@[simp]
lemma concatSumPerm_apply {j k r : ℕ} (L : PartialPairing j r) (R : PartialPairing k r)
    (σ : Equiv.Perm (Fin r)) (x : Fin j ⊕ Fin k) :
    concatSumPerm L R σ x = concatSumFun L R σ x := rfl

def concatRev {j k r : ℕ} (L : PartialPairing j r) (R : PartialPairing k r)
    (σ : Equiv.Perm (Fin r)) : ChordPairing (j + k) where
  mate := (concatSlotEquiv j k).symm.trans
    ((concatSumPerm L R σ).trans (concatSlotEquiv j k))
  involutive x := by
    change concatSlotEquiv j k (concatSumFun L R σ
      ((concatSlotEquiv j k).symm (concatSlotEquiv j k
        (concatSumFun L R σ ((concatSlotEquiv j k).symm x))))) = x
    rw [Equiv.symm_apply_apply, concatSumFun_involutive L R σ, Equiv.apply_symm_apply]
  ne_self x h := by
    have h' := (concatSlotEquiv j k).injective
      (h.trans ((concatSlotEquiv j k).apply_symm_apply x).symm)
    exact concatSumFun_ne_self L R σ ((concatSlotEquiv j k).symm x) h'

@[simp]
lemma concatRev_mate_slot {j k r : ℕ} (L : PartialPairing j r) (R : PartialPairing k r)
    (σ : Equiv.Perm (Fin r)) (x : Fin j ⊕ Fin k) :
    (concatRev L R σ).mate (concatSlotEquiv j k x) =
      concatSlotEquiv j k (concatSumFun L R σ x) := by
  change concatSlotEquiv j k (concatSumFun L R σ ((concatSlotEquiv j k).symm
    (concatSlotEquiv j k x))) = _
  rw [Equiv.symm_apply_apply]

def concatRevChordMap {j k r : ℕ} (L : PartialPairing j r) (R : PartialPairing k r)
    (σ : Equiv.Perm (Fin r)) :
    (L.InternalChord ⊕ R.InternalChord) ⊕ Fin r → (concatRev L R σ).Chord
  | Sum.inl (Sum.inl cL) =>
      ⟨concatSlotEquiv j k (Sum.inl (L.mate cL.1)), by
        rw [concatRev_mate_slot]
        dsimp [concatSumFun]
        rw [dif_neg (L.mate_mate_ne_of_internalChord cL), L.mate_mate,
            concatSlotEquiv_inl_lt_inl]
        exact cL.2⟩
  | Sum.inl (Sum.inr cR) =>
      ⟨concatSlotEquiv j k (Sum.inr cR.1), by
        rw [concatRev_mate_slot]
        dsimp [concatSumFun]
        rw [dif_neg (R.mate_ne_self_of_internalChord cR), concatSlotEquiv_inr_lt_inr]
        exact cR.2⟩
  | Sum.inr a =>
      ⟨concatSlotEquiv j k (Sum.inl (L.unpaired a)), by
        rw [concatRev_mate_slot]
        dsimp [concatSumFun]
        rw [dif_pos (L.mate_unpaired a)]
        exact concatSlotEquiv_inl_lt_inr _ _⟩

def concatRevChordInvAux {j k r : ℕ} (L : PartialPairing j r) (R : PartialPairing k r)
    (σ : Equiv.Perm (Fin r)) :
    (s : Fin j ⊕ Fin k) →
    (concatSlotEquiv j k s < (concatRev L R σ).mate (concatSlotEquiv j k s)) →
    (L.InternalChord ⊕ R.InternalChord) ⊕ Fin r
  | Sum.inl i, hs =>
      if h : L.mate i = i then
        Sum.inr (L.unpairedIdx i h)
      else
        Sum.inl (Sum.inl ⟨L.mate i, by
          rw [concatRev_mate_slot] at hs
          dsimp only [concatSumFun] at hs
          rw [dif_neg h, concatSlotEquiv_inl_lt_inl] at hs
          rwa [L.mate_mate]⟩)
  | Sum.inr t, hs =>
      Sum.inl (Sum.inr ⟨t, by
        rw [concatRev_mate_slot] at hs
        dsimp only [concatSumFun] at hs
        split_ifs at hs with h
        · exact False.elim (not_concatSlotEquiv_inr_lt_inl t _ hs)
        · rwa [concatSlotEquiv_inr_lt_inr] at hs⟩)

lemma concatRevChordInvAux_congr {j k r : ℕ} (L : PartialPairing j r) (R : PartialPairing k r)
    (σ : Equiv.Perm (Fin r)) {s₁ s₂ : Fin j ⊕ Fin k} (h : s₁ = s₂)
    (hs₁ : concatSlotEquiv j k s₁ < (concatRev L R σ).mate (concatSlotEquiv j k s₁))
    (hs₂ : concatSlotEquiv j k s₂ < (concatRev L R σ).mate (concatSlotEquiv j k s₂)) :
    concatRevChordInvAux L R σ s₁ hs₁ = concatRevChordInvAux L R σ s₂ hs₂ := by
  cases h
  rfl

def concatRevChordInv {j k r : ℕ} (L : PartialPairing j r) (R : PartialPairing k r)
    (σ : Equiv.Perm (Fin r)) (c : (concatRev L R σ).Chord) :
    (L.InternalChord ⊕ R.InternalChord) ⊕ Fin r :=
  concatRevChordInvAux L R σ ((concatSlotEquiv j k).symm c.1) (by
    rw [(concatSlotEquiv j k).apply_symm_apply]
    exact c.2)

lemma concatRevChordInv_slot {j k r : ℕ} (L : PartialPairing j r) (R : PartialPairing k r)
    (σ : Equiv.Perm (Fin r)) (s : Fin j ⊕ Fin k)
    (hs : concatSlotEquiv j k s < (concatRev L R σ).mate (concatSlotEquiv j k s)) :
    concatRevChordInv L R σ ⟨concatSlotEquiv j k s, hs⟩ =
      concatRevChordInvAux L R σ s hs :=
  concatRevChordInvAux_congr L R σ ((concatSlotEquiv j k).symm_apply_apply s) _ hs

def concatRevChordEquiv {j k r : ℕ} (L : PartialPairing j r) (R : PartialPairing k r)
    (σ : Equiv.Perm (Fin r)) :
    ((L.InternalChord ⊕ R.InternalChord) ⊕ Fin r) ≃ (concatRev L R σ).Chord where
  toFun := concatRevChordMap L R σ
  invFun := concatRevChordInv L R σ
  left_inv := by
    rintro ((cL | cR) | a)
    · rw [concatRevChordMap, concatRevChordInv_slot]
      dsimp [concatRevChordInvAux]
      rw [dif_neg (L.mate_mate_ne_of_internalChord cL)]
      exact congrArg (Sum.inl ∘ Sum.inl) (Subtype.ext (L.mate_mate cL.1))
    · rw [concatRevChordMap, concatRevChordInv_slot]
      rfl
    · rw [concatRevChordMap, concatRevChordInv_slot]
      dsimp [concatRevChordInvAux]
      rw [dif_pos (L.mate_unpaired a), L.unpairedIdx_unpaired]
  right_inv := by
    intro c
    let s := (concatSlotEquiv j k).symm c.1
    have hs_eq : concatSlotEquiv j k s = c.1 := (concatSlotEquiv j k).apply_symm_apply c.1
    have hs_lt : concatSlotEquiv j k s < (concatRev L R σ).mate (concatSlotEquiv j k s) := by
      rw [hs_eq]
      exact c.2
    have hc_eq : c = ⟨concatSlotEquiv j k s, hs_lt⟩ := Subtype.ext hs_eq.symm
    rw [hc_eq, concatRevChordInv_slot]
    apply Subtype.ext
    rcases s with i | t
    · dsimp [concatRevChordInvAux]
      split_ifs with h
      · dsimp [concatRevChordMap]
        rw [L.unpaired_unpairedIdx]
      · dsimp [concatRevChordMap]
        rw [L.mate_mate]
    · rfl

def splitSumPerm {j k : ℕ} (P : ChordPairing (j + k)) : Equiv.Perm (Fin j ⊕ Fin k) :=
  (concatSlotEquiv j k).trans (P.mate.trans (concatSlotEquiv j k).symm)

lemma splitSumPerm_involutive {j k : ℕ} (P : ChordPairing (j + k)) :
    Function.Involutive (splitSumPerm P) := by
  intro x
  change (concatSlotEquiv j k).symm (P.mate (concatSlotEquiv j k
    ((concatSlotEquiv j k).symm (P.mate (concatSlotEquiv j k x))))) = x
  rw [Equiv.apply_symm_apply, P.mate_mate, Equiv.symm_apply_apply]

lemma splitSumPerm_ne_self {j k : ℕ} (P : ChordPairing (j + k)) (x : Fin j ⊕ Fin k) :
    splitSumPerm P x ≠ x := by
  intro h
  have h' : P.mate (concatSlotEquiv j k x) = concatSlotEquiv j k x := by
    have := congrArg (concatSlotEquiv j k) h
    simpa [splitSumPerm] using this
  exact P.ne_self _ h'

def splitLeftSet {j k : ℕ} (P : ChordPairing (j + k)) : Finset (Fin j) :=
  Finset.univ.filter (fun i : Fin j => (splitSumPerm P (Sum.inl i)).isRight = true)

def splitRightSet {j k : ℕ} (P : ChordPairing (j + k)) : Finset (Fin k) :=
  Finset.univ.filter (fun t : Fin k => (splitSumPerm P (Sum.inr t)).isLeft = true)

lemma exists_inr_of_mem_splitLeftSet {j k : ℕ} (P : ChordPairing (j + k))
    {i : Fin j} (hi : i ∈ splitLeftSet P) :
    ∃ t : Fin k, splitSumPerm P (Sum.inl i) = Sum.inr t := by
  rw [splitLeftSet, Finset.mem_filter] at hi
  rcases h : splitSumPerm P (Sum.inl i) with _ | t
  · rw [h] at hi
    exact False.elim (Bool.false_ne_true hi.2)
  · exact ⟨t, rfl⟩

lemma exists_inl_of_mem_splitRightSet {j k : ℕ} (P : ChordPairing (j + k))
    {t : Fin k} (ht : t ∈ splitRightSet P) :
    ∃ i : Fin j, splitSumPerm P (Sum.inr t) = Sum.inl i := by
  rw [splitRightSet, Finset.mem_filter] at ht
  rcases h : splitSumPerm P (Sum.inr t) with i | _
  · exact ⟨i, rfl⟩
  · rw [h] at ht
    exact False.elim (Bool.false_ne_true ht.2)

def splitCrossRight {j k : ℕ} (P : ChordPairing (j + k))
    (i : Fin j) (hi : i ∈ splitLeftSet P) : Fin k :=
  Classical.choose (exists_inr_of_mem_splitLeftSet P hi)

@[simp]
lemma splitSumPerm_inl_splitCrossRight {j k : ℕ} (P : ChordPairing (j + k))
    (i : Fin j) (hi : i ∈ splitLeftSet P) :
    splitSumPerm P (Sum.inl i) = Sum.inr (splitCrossRight P i hi) :=
  Classical.choose_spec (exists_inr_of_mem_splitLeftSet P hi)

lemma splitCrossRight_mem {j k : ℕ} (P : ChordPairing (j + k))
    (i : Fin j) (hi : i ∈ splitLeftSet P) :
    splitCrossRight P i hi ∈ splitRightSet P := by
  rw [splitRightSet, Finset.mem_filter]
  have hinv := splitSumPerm_involutive P (Sum.inl i)
  rw [splitSumPerm_inl_splitCrossRight P i hi] at hinv
  rw [hinv]
  exact ⟨Finset.mem_univ _, rfl⟩

def splitCrossLeft {j k : ℕ} (P : ChordPairing (j + k))
    (t : Fin k) (ht : t ∈ splitRightSet P) : Fin j :=
  Classical.choose (exists_inl_of_mem_splitRightSet P ht)

@[simp]
lemma splitSumPerm_inr_splitCrossLeft {j k : ℕ} (P : ChordPairing (j + k))
    (t : Fin k) (ht : t ∈ splitRightSet P) :
    splitSumPerm P (Sum.inr t) = Sum.inl (splitCrossLeft P t ht) :=
  Classical.choose_spec (exists_inl_of_mem_splitRightSet P ht)

lemma splitCrossLeft_mem {j k : ℕ} (P : ChordPairing (j + k))
    (t : Fin k) (ht : t ∈ splitRightSet P) :
    splitCrossLeft P t ht ∈ splitLeftSet P := by
  rw [splitLeftSet, Finset.mem_filter]
  have hinv := splitSumPerm_involutive P (Sum.inr t)
  rw [splitSumPerm_inr_splitCrossLeft P t ht] at hinv
  rw [hinv]
  exact ⟨Finset.mem_univ _, rfl⟩

@[simp]
lemma splitCrossLeft_splitCrossRight {j k : ℕ} (P : ChordPairing (j + k))
    (i : Fin j) (hi : i ∈ splitLeftSet P)
    (ht : splitCrossRight P i hi ∈ splitRightSet P := splitCrossRight_mem P i hi) :
    splitCrossLeft P (splitCrossRight P i hi) ht = i := by
  have hinv := splitSumPerm_involutive P (Sum.inl i)
  rw [splitSumPerm_inl_splitCrossRight P i hi,
      splitSumPerm_inr_splitCrossLeft P _ ht] at hinv
  exact Sum.inl.inj hinv

@[simp]
lemma splitCrossRight_splitCrossLeft {j k : ℕ} (P : ChordPairing (j + k))
    (t : Fin k) (ht : t ∈ splitRightSet P)
    (hi : splitCrossLeft P t ht ∈ splitLeftSet P := splitCrossLeft_mem P t ht) :
    splitCrossRight P (splitCrossLeft P t ht) hi = t := by
  have hinv := splitSumPerm_involutive P (Sum.inr t)
  rw [splitSumPerm_inr_splitCrossLeft P t ht,
      splitSumPerm_inl_splitCrossRight P _ hi] at hinv
  exact Sum.inr.inj hinv

lemma card_splitLeftSet_eq_card_splitRightSet {j k : ℕ} (P : ChordPairing (j + k)) :
    (splitLeftSet P).card = (splitRightSet P).card := by
  apply Finset.card_bij (fun (i : Fin j) hi => splitCrossRight P i hi)
  · intro i hi
    exact splitCrossRight_mem P i hi
  · intro i1 hi1 i2 hi2 h_eq
    have h1 := splitCrossLeft_splitCrossRight P i1 hi1
    have h2 := splitCrossLeft_splitCrossRight P i2 hi2
    have hcongr : splitCrossLeft P (splitCrossRight P i1 hi1) (splitCrossRight_mem P i1 hi1) =
        splitCrossLeft P (splitCrossRight P i2 hi2) (splitCrossRight_mem P i2 hi2) := by
      congr 1
    exact h1.symm.trans (hcongr.trans h2)
  · intro t ht
    exact ⟨splitCrossLeft P t ht, splitCrossLeft_mem P t ht, splitCrossRight_splitCrossLeft P t ht⟩

lemma card_splitLeftSet_le_min {j k : ℕ} (P : ChordPairing (j + k)) :
    (splitLeftSet P).card ≤ min j k := by
  refine le_min ?_ ?_
  · simpa using Finset.card_le_univ (splitLeftSet P)
  · rw [card_splitLeftSet_eq_card_splitRightSet]
    simpa using Finset.card_le_univ (splitRightSet P)

def splitLeftMateFun {j k : ℕ} (P : ChordPairing (j + k)) (i : Fin j) : Fin j :=
  match splitSumPerm P (Sum.inl i) with
  | Sum.inl i' => i'
  | Sum.inr _ => i

lemma splitLeftMateFun_involutive {j k : ℕ} (P : ChordPairing (j + k)) :
    Function.Involutive (splitLeftMateFun P) := by
  intro i
  dsimp [splitLeftMateFun]
  rcases h : splitSumPerm P (Sum.inl i) with i' | t
  · dsimp only
    have hinv := splitSumPerm_involutive P (Sum.inl i)
    rw [h] at hinv
    rw [hinv]
  · dsimp only
    rw [h]

def splitRightMateFun {j k : ℕ} (P : ChordPairing (j + k)) (t : Fin k) : Fin k :=
  match splitSumPerm P (Sum.inr t) with
  | Sum.inl _ => t
  | Sum.inr t' => t'

lemma splitRightMateFun_involutive {j k : ℕ} (P : ChordPairing (j + k)) :
    Function.Involutive (splitRightMateFun P) := by
  intro t
  dsimp [splitRightMateFun]
  rcases h : splitSumPerm P (Sum.inr t) with i | t'
  · dsimp only
    rw [h]
  · dsimp only
    have hinv := splitSumPerm_involutive P (Sum.inr t)
    rw [h] at hinv
    rw [hinv]

def splitLeftPartial {j k : ℕ} (P : ChordPairing (j + k)) :
    PartialPairing j (splitLeftSet P).card where
  unpaired := (splitLeftSet P).orderEmbOfFin rfl
  strictMono_unpaired := ((splitLeftSet P).orderEmbOfFin rfl).strictMono
  mate :=
    { toFun := splitLeftMateFun P
      invFun := splitLeftMateFun P
      left_inv := splitLeftMateFun_involutive P
      right_inv := splitLeftMateFun_involutive P }
  involutive := splitLeftMateFun_involutive P
  fixed_iff := fun i => by
    change splitLeftMateFun P i = i ↔
      ∃ a : Fin (splitLeftSet P).card, (splitLeftSet P).orderEmbOfFin rfl a = i
    have hrange : (∃ a, (splitLeftSet P).orderEmbOfFin rfl a = i) ↔ i ∈ splitLeftSet P := by
      rw [← Set.mem_range, Finset.range_orderEmbOfFin]
      rfl
    rw [hrange, splitLeftSet, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    dsimp [splitLeftMateFun]
    rcases h : splitSumPerm P (Sum.inl i) with i' | t
    · simp only [Sum.isRight_inl, Bool.false_eq_true, iff_false]
      intro hi'
      rw [hi'] at h
      exact splitSumPerm_ne_self P (Sum.inl i) h
    · simp

def splitRightPartial {j k : ℕ} (P : ChordPairing (j + k)) :
    PartialPairing k (splitLeftSet P).card :=
  let hr : (splitRightSet P).card = (splitLeftSet P).card :=
    (card_splitLeftSet_eq_card_splitRightSet P).symm
  { unpaired := (splitRightSet P).orderEmbOfFin hr
    strictMono_unpaired := ((splitRightSet P).orderEmbOfFin hr).strictMono
    mate :=
      { toFun := splitRightMateFun P
        invFun := splitRightMateFun P
        left_inv := splitRightMateFun_involutive P
        right_inv := splitRightMateFun_involutive P }
    involutive := splitRightMateFun_involutive P
    fixed_iff := fun t => by
      change splitRightMateFun P t = t ↔
        ∃ b : Fin (splitLeftSet P).card, (splitRightSet P).orderEmbOfFin hr b = t
      have hrange : (∃ b, (splitRightSet P).orderEmbOfFin hr b = t) ↔ t ∈ splitRightSet P := by
        rw [← Set.mem_range, Finset.range_orderEmbOfFin]
        rfl
      rw [hrange, splitRightSet, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and]
      dsimp [splitRightMateFun]
      rcases h : splitSumPerm P (Sum.inr t) with i | t'
      · simp
      · simp only [Sum.isLeft_inr, Bool.false_eq_true, iff_false]
        intro ht'
        rw [ht'] at h
        exact splitSumPerm_ne_self P (Sum.inr t) h }

lemma splitCrossLeft_congr {j k : ℕ} (P : ChordPairing (j + k))
    {t₁ t₂ : Fin k} (h : t₁ = t₂) (ht₁ : t₁ ∈ splitRightSet P) (ht₂ : t₂ ∈ splitRightSet P) :
    splitCrossLeft P t₁ ht₁ = splitCrossLeft P t₂ ht₂ := by
  cases h
  rfl

lemma splitCrossRight_congr {j k : ℕ} (P : ChordPairing (j + k))
    {i₁ i₂ : Fin j} (h : i₁ = i₂) (hi₁ : i₁ ∈ splitLeftSet P) (hi₂ : i₂ ∈ splitLeftSet P) :
    splitCrossRight P i₁ hi₁ = splitCrossRight P i₂ hi₂ := by
  cases h
  rfl

lemma splitRightPartial_mate_of_mem {j k : ℕ} (P : ChordPairing (j + k))
    {t : Fin k} (ht : t ∈ splitRightSet P) :
    (splitRightPartial P).mate t = t := by
  change splitRightMateFun P t = t
  dsimp [splitRightMateFun]
  rw [splitSumPerm_inr_splitCrossLeft P t ht]

lemma splitLeftPartial_mate_of_mem {j k : ℕ} (P : ChordPairing (j + k))
    {i : Fin j} (hi : i ∈ splitLeftSet P) :
    (splitLeftPartial P).mate i = i := by
  change splitLeftMateFun P i = i
  dsimp [splitLeftMateFun]
  rw [splitSumPerm_inl_splitCrossRight P i hi]

def splitPermFun {j k : ℕ} (P : ChordPairing (j + k))
    (a : Fin (splitLeftSet P).card) : Fin (splitLeftSet P).card :=
  let hi : (splitLeftPartial P).unpaired a ∈ splitLeftSet P :=
    Finset.orderEmbOfFin_mem (splitLeftSet P) rfl a
  let t := splitCrossRight P ((splitLeftPartial P).unpaired a) hi
  (splitRightPartial P).unpairedIdx t (splitRightPartial_mate_of_mem P (splitCrossRight_mem P _ hi))

def splitPermInvFun {j k : ℕ} (P : ChordPairing (j + k))
    (b : Fin (splitLeftSet P).card) : Fin (splitLeftSet P).card :=
  let hr : (splitRightSet P).card = (splitLeftSet P).card :=
    (card_splitLeftSet_eq_card_splitRightSet P).symm
  let ht : (splitRightPartial P).unpaired b ∈ splitRightSet P :=
    Finset.orderEmbOfFin_mem (splitRightSet P) hr b
  let i := splitCrossLeft P ((splitRightPartial P).unpaired b) ht
  (splitLeftPartial P).unpairedIdx i (splitLeftPartial_mate_of_mem P (splitCrossLeft_mem P _ ht))

def splitPerm {j k : ℕ} (P : ChordPairing (j + k)) :
    Equiv.Perm (Fin (splitLeftSet P).card) where
  toFun := splitPermFun P
  invFun := splitPermInvFun P
  left_inv a := by
    apply (splitLeftPartial P).unpaired_injective
    dsimp [splitPermInvFun, splitPermFun]
    rw [(splitLeftPartial P).unpaired_unpairedIdx]
    let hi := Finset.orderEmbOfFin_mem (splitLeftSet P) rfl a
    exact (splitCrossLeft_congr P ((splitRightPartial P).unpaired_unpairedIdx _ _) _
      (splitCrossRight_mem P _ hi)).trans (splitCrossLeft_splitCrossRight P _ hi)
  right_inv b := by
    apply (splitRightPartial P).unpaired_injective
    dsimp [splitPermFun, splitPermInvFun]
    rw [(splitRightPartial P).unpaired_unpairedIdx]
    let hr : (splitRightSet P).card = (splitLeftSet P).card :=
      (card_splitLeftSet_eq_card_splitRightSet P).symm
    let ht := Finset.orderEmbOfFin_mem (splitRightSet P) hr b
    exact (splitCrossRight_congr P ((splitLeftPartial P).unpaired_unpairedIdx _ _) _
      (splitCrossLeft_mem P _ ht)).trans (splitCrossRight_splitCrossLeft P _ ht)

lemma concatRev_split {j k : ℕ} (P : ChordPairing (j + k)) :
    concatRev (splitLeftPartial P) (splitRightPartial P) (splitPerm P) = P := by
  apply ChordPairing.ext
  apply Equiv.ext
  intro x
  have hx : x = concatSlotEquiv j k ((concatSlotEquiv j k).symm x) :=
    ((concatSlotEquiv j k).apply_symm_apply x).symm
  rw [hx, concatRev_mate_slot]
  rcases y : (concatSlotEquiv j k).symm x with i | t
  · dsimp [concatSumFun]
    split_ifs with h
    · have hi_mem : i ∈ splitLeftSet P := by
        rcases ((splitLeftPartial P).fixed_iff i).mp h with ⟨a, rfl⟩
        exact Finset.orderEmbOfFin_mem (splitLeftSet P) rfl a
      change concatSlotEquiv j k (Sum.inr ((splitRightPartial P).unpaired
        (splitPermFun P ((splitLeftPartial P).unpairedIdx i h)))) = _
      dsimp [splitPermFun]
      rw [(splitRightPartial P).unpaired_unpairedIdx]
      have hi_eq : (splitLeftPartial P).unpaired ((splitLeftPartial P).unpairedIdx i h) = i :=
        (splitLeftPartial P).unpaired_unpairedIdx i h
      have hcr : splitCrossRight P
          ((splitLeftPartial P).unpaired ((splitLeftPartial P).unpairedIdx i h))
          (Finset.orderEmbOfFin_mem (splitLeftSet P) rfl _) =
          splitCrossRight P i hi_mem := by
        congr 1
      rw [hcr]
      have hm := congrArg (concatSlotEquiv j k) (splitSumPerm_inl_splitCrossRight P i hi_mem)
      simpa [splitSumPerm] using hm.symm
    · have hm_left : ∃ i', splitSumPerm P (Sum.inl i) = Sum.inl i' := by
        rcases hm : splitSumPerm P (Sum.inl i) with i' | t'
        · exact ⟨i', rfl⟩
        · exfalso
          apply h
          change splitLeftMateFun P i = i
          simp [splitLeftMateFun, hm]
      rcases hm_left with ⟨i', hm⟩
      have hmate : (splitLeftPartial P).mate i = i' := by
        change splitLeftMateFun P i = i'
        simp [splitLeftMateFun, hm]
      rw [hmate]
      have hm' := congrArg (concatSlotEquiv j k) hm
      simpa [splitSumPerm] using hm'.symm
  · dsimp [concatSumFun]
    split_ifs with h
    · have hr : (splitRightSet P).card = (splitLeftSet P).card :=
        (card_splitLeftSet_eq_card_splitRightSet P).symm
      have ht_mem : t ∈ splitRightSet P := by
        rcases ((splitRightPartial P).fixed_iff t).mp h with ⟨b, rfl⟩
        exact Finset.orderEmbOfFin_mem (splitRightSet P) hr b
      change concatSlotEquiv j k (Sum.inl ((splitLeftPartial P).unpaired
        (splitPermInvFun P ((splitRightPartial P).unpairedIdx t h)))) = _
      dsimp [splitPermInvFun]
      rw [(splitLeftPartial P).unpaired_unpairedIdx]
      have ht_eq : (splitRightPartial P).unpaired ((splitRightPartial P).unpairedIdx t h) = t :=
        (splitRightPartial P).unpaired_unpairedIdx t h
      have hcl : splitCrossLeft P
          ((splitRightPartial P).unpaired ((splitRightPartial P).unpairedIdx t h))
          (Finset.orderEmbOfFin_mem (splitRightSet P) hr _) =
          splitCrossLeft P t ht_mem := by
        congr 1
      rw [hcl]
      have hm := congrArg (concatSlotEquiv j k) (splitSumPerm_inr_splitCrossLeft P t ht_mem)
      simpa [splitSumPerm] using hm.symm
    · have hm_right : ∃ t', splitSumPerm P (Sum.inr t) = Sum.inr t' := by
        rcases hm : splitSumPerm P (Sum.inr t) with i' | t'
        · exfalso
          apply h
          change splitRightMateFun P t = t
          simp [splitRightMateFun, hm]
        · exact ⟨t', rfl⟩
      rcases hm_right with ⟨t', hm⟩
      have hmate : (splitRightPartial P).mate t = t' := by
        change splitRightMateFun P t = t'
        simp [splitRightMateFun, hm]
      rw [hmate]
      have hm' := congrArg (concatSlotEquiv j k) hm
      simpa [splitSumPerm] using hm'.symm

lemma splitSumPerm_concatRev {j k r : ℕ} (L : PartialPairing j r) (R : PartialPairing k r)
    (σ : Equiv.Perm (Fin r)) :
    splitSumPerm (concatRev L R σ) = concatSumPerm L R σ := by
  apply Equiv.ext
  intro x
  change (concatSlotEquiv j k).symm ((concatRev L R σ).mate (concatSlotEquiv j k x)) =
    concatSumFun L R σ x
  rw [concatRev_mate_slot, Equiv.symm_apply_apply]

lemma splitLeftSet_concatRev {j k r : ℕ} (L : PartialPairing j r) (R : PartialPairing k r)
    (σ : Equiv.Perm (Fin r)) :
    splitLeftSet (concatRev L R σ) =
      Finset.univ.map ⟨L.unpaired, L.unpaired_injective⟩ := by
  ext i
  rw [splitLeftSet, Finset.mem_filter, splitSumPerm_concatRev]
  simp only [Finset.mem_univ, true_and, concatSumPerm_apply, Finset.mem_map,
    Function.Embedding.coeFn_mk]
  dsimp [concatSumFun]
  split_ifs with h
  · exact ⟨fun _ => (L.fixed_iff i).mp h, fun _ => rfl⟩
  · simp only [Sum.isRight_inl, Bool.false_eq_true, false_iff]
    intro hex
    exact h ((L.fixed_iff i).mpr hex)

lemma card_splitLeftSet_concatRev {j k r : ℕ} (L : PartialPairing j r)
    (R : PartialPairing k r) (σ : Equiv.Perm (Fin r)) :
    (splitLeftSet (concatRev L R σ)).card = r := by
  rw [splitLeftSet_concatRev, Finset.card_map, Finset.card_univ, Fintype.card_fin]

lemma cast_partial_mate {n r₁ r₂ : ℕ} (h : r₁ = r₂) (M : PartialPairing n r₁) :
    (h ▸ M).mate = M.mate := by
  cases h
  rfl

lemma cast_partial_unpaired {n r₁ r₂ : ℕ} (h : r₁ = r₂) (M : PartialPairing n r₁)
    (a : Fin r₂) :
    (h ▸ M).unpaired a = M.unpaired (Fin.cast h.symm a) := by
  cases h
  rfl

lemma cast_perm_apply {r₁ r₂ : ℕ} (h : r₁ = r₂) (π : Equiv.Perm (Fin r₁)) (a : Fin r₂) :
    (h ▸ π : Equiv.Perm (Fin r₂)) a = Fin.cast h (π (Fin.cast h.symm a)) := by
  cases h
  rfl

lemma cast_prod3_heq {j k r₁ r₂ : ℕ} (h : r₁ = r₂)
    (x : PartialPairing j r₁) (y : PartialPairing k r₁) (z : Equiv.Perm (Fin r₁)) :
    (x, y, z) ≍
      ((h ▸ x : PartialPairing j r₂),
       (h ▸ y : PartialPairing k r₂),
       (h ▸ z : Equiv.Perm (Fin r₂))) := by
  cases h
  rfl

def chordPairingConcatRevEquiv (j k : ℕ) :
    (Σ r : Fin (min j k + 1),
      PartialPairing j r.val × PartialPairing k r.val × Equiv.Perm (Fin r.val)) ≃
    ChordPairing (j + k) where
  toFun x := concatRev x.2.1 x.2.2.1 x.2.2.2
  invFun P :=
    ⟨⟨(splitLeftSet P).card, Nat.lt_succ_of_le (card_splitLeftSet_le_min P)⟩,
      (splitLeftPartial P, splitRightPartial P, splitPerm P)⟩
  right_inv P := concatRev_split P
  left_inv := by
    rintro ⟨⟨r, hr_lt⟩, L, R, σ⟩
    let P := concatRev L R σ
    have hcard : (splitLeftSet P).card = r := card_splitLeftSet_concatRev L R σ
    refine Sigma.ext (Fin.ext hcard) ?_
    refine (cast_prod3_heq hcard (splitLeftPartial P) (splitRightPartial P) (splitPerm P)).trans
      (heq_of_eq ?_)
    have hL : (hcard ▸ splitLeftPartial P : PartialPairing j r) = L := by
      apply ext_mate
      rw [cast_partial_mate]
      apply Equiv.ext
      intro i
      change splitLeftMateFun P i = L.mate i
      dsimp [splitLeftMateFun, P]
      rw [splitSumPerm_concatRev]
      dsimp [concatSumPerm, concatSumFun]
      split_ifs with h
      · exact h.symm
      · rfl
    have hR : (hcard ▸ splitRightPartial P : PartialPairing k r) = R := by
      apply ext_mate
      rw [cast_partial_mate]
      apply Equiv.ext
      intro t
      change splitRightMateFun P t = R.mate t
      dsimp [splitRightMateFun, P]
      rw [splitSumPerm_concatRev]
      dsimp [concatSumPerm, concatSumFun]
      split_ifs with h
      · exact h.symm
      · rfl
    have hσ : (hcard ▸ splitPerm P : Equiv.Perm (Fin r)) = σ := by
      apply Equiv.ext
      intro a
      apply R.unpaired_injective
      have hb : R.unpaired ((hcard ▸ splitPerm P : Equiv.Perm (Fin r)) a) =
          (splitRightPartial P).unpaired (splitPermFun P (Fin.cast hcard.symm a)) := by
        rw [← hR, cast_partial_unpaired, cast_perm_apply]
        congr 1
      rw [hb]
      dsimp [splitPermFun]
      rw [(splitRightPartial P).unpaired_unpairedIdx]
      let a' := Fin.cast hcard.symm a
      have hi_mem : (splitLeftPartial P).unpaired a' ∈ splitLeftSet P :=
        Finset.orderEmbOfFin_mem (splitLeftSet P) rfl a'
      have huLa : (splitLeftPartial P).unpaired a' = L.unpaired a := by
        have := congrFun (congrArg PartialPairing.unpaired hL) a
        simpa [cast_partial_unpaired, a'] using this
      have hm : Sum.inr (splitCrossRight P ((splitLeftPartial P).unpaired a') hi_mem) =
          splitSumPerm P (Sum.inl (L.unpaired a)) := by
        rw [← splitSumPerm_inl_splitCrossRight P ((splitLeftPartial P).unpaired a') hi_mem, huLa]
      dsimp [P] at hm
      rw [splitSumPerm_concatRev] at hm
      dsimp [concatSumPerm, concatSumFun] at hm
      rw [dif_pos (L.mate_unpaired a), L.unpairedIdx_unpaired] at hm
      exact Sum.inr.inj hm
    exact Prod.ext hL (Prod.ext hR hσ)

theorem cross_concatRev {j k r : ℕ} (L : PartialPairing j r) (R : PartialPairing k r)
    (σ : Equiv.Perm (Fin r)) :
    (concatRev L R σ).cross = L.partialCross + R.partialCross + permInversions σ := by
  let P := concatRev L R σ
  let e := concatSlotEquiv j k
  let M := concatSumFun L R σ
  let pred : (Fin j ⊕ Fin k) × (Fin j ⊕ Fin k) → Prop := fun xy =>
    e xy.1 < e xy.2 ∧ e xy.2 < e (M xy.1) ∧ e (M xy.1) < e (M xy.2)
  haveI : DecidablePred pred := Classical.decPred pred
  have h_pull : P.cross = (Finset.univ.filter pred).card := by
    dsimp [ChordPairing.cross]
    apply Finset.card_bij (fun (uv : Fin (j + k) × Fin (j + k)) _ => (e.symm uv.1, e.symm uv.2))
    · intro ⟨u, v⟩ huv
      rw [Finset.mem_filter] at huv ⊢
      rcases huv with ⟨_, h1, h2, h3⟩
      dsimp [pred]
      have hu : e (e.symm u) = u := e.apply_symm_apply u
      have hv : e (e.symm v) = v := e.apply_symm_apply v
      have hmu : e (M (e.symm u)) = P.mate u := by
        dsimp [M, P]
        rw [← concatRev_mate_slot, hu]
      have hmv : e (M (e.symm v)) = P.mate v := by
        dsimp [M, P]
        rw [← concatRev_mate_slot, hv]
      rw [hu, hv, hmu, hmv]
      exact ⟨Finset.mem_univ _, h1, h2, h3⟩
    · intro ⟨u1, v1⟩ _ ⟨u2, v2⟩ _ h_eq
      rcases Prod.mk.inj h_eq with ⟨h1, h2⟩
      exact Prod.ext (e.symm.injective h1) (e.symm.injective h2)
    · intro ⟨x, y⟩ hxy
      rw [Finset.mem_filter] at hxy
      rcases hxy with ⟨_, h1, h2, h3⟩
      refine ⟨(e x, e y), ?_, by simp⟩
      rw [Finset.mem_filter]
      dsimp [P]
      rw [concatRev_mate_slot, concatRev_mate_slot]
      exact ⟨Finset.mem_univ _, h1, h2, h3⟩
  let embLLInt : (Fin j × Fin j) ↪ (Fin j ⊕ Fin k) × (Fin j ⊕ Fin k) :=
    ⟨fun uv => (Sum.inl (L.mate uv.2), Sum.inl (L.mate uv.1)), fun a b h => by
      rcases Prod.mk.inj h with ⟨h1, h2⟩
      exact Prod.ext (L.mate.injective (Sum.inl.inj h2)) (L.mate.injective (Sum.inl.inj h1))⟩
  let embLLOpen : (Fin j × Fin r) ↪ (Fin j ⊕ Fin k) × (Fin j ⊕ Fin k) :=
    ⟨fun ua => (Sum.inl (L.mate ua.1), Sum.inl (L.unpaired ua.2)), fun a b h => by
      rcases Prod.mk.inj h with ⟨h1, h2⟩
      exact Prod.ext (L.mate.injective (Sum.inl.inj h1))
        (L.unpaired_injective (Sum.inl.inj h2))⟩
  let embLLCC : (Fin r × Fin r) ↪ (Fin j ⊕ Fin k) × (Fin j ⊕ Fin k) :=
    ⟨fun aa => (Sum.inl (L.unpaired aa.2), Sum.inl (L.unpaired aa.1)), fun a b h => by
      rcases Prod.mk.inj h with ⟨h1, h2⟩
      exact Prod.ext (L.unpaired_injective (Sum.inl.inj h2))
        (L.unpaired_injective (Sum.inl.inj h1))⟩
  let embLR : (Fin k × Fin r) ↪ (Fin j ⊕ Fin k) × (Fin j ⊕ Fin k) :=
    ⟨fun tb => (Sum.inl (L.unpaired (σ.symm tb.2)), Sum.inr tb.1), fun a b h => by
      rcases Prod.mk.inj h with ⟨h1, h2⟩
      exact Prod.ext (Sum.inr.inj h2) (σ.symm.injective (L.unpaired_injective (Sum.inl.inj h1)))⟩
  let embRR : (Fin k × Fin k) ↪ (Fin j ⊕ Fin k) × (Fin j ⊕ Fin k) :=
    ⟨fun tt => (Sum.inr tt.1, Sum.inr tt.2), fun a b h => by
      rcases Prod.mk.inj h with ⟨h1, h2⟩
      exact Prod.ext (Sum.inr.inj h1) (Sum.inr.inj h2)⟩
  let F_LL_int := (Finset.univ.filter (fun ij : Fin j × Fin j =>
    ij.1 < ij.2 ∧ ij.2 < L.mate ij.1 ∧ L.mate ij.1 < L.mate ij.2)).map embLLInt
  let F_LL_open := (Finset.univ.filter (fun ca : Fin j × Fin r =>
    ca.1 < L.unpaired ca.2 ∧ L.unpaired ca.2 < L.mate ca.1)).map embLLOpen
  let F_LL_cc := (Finset.univ.filter (fun ij : Fin r × Fin r =>
    ij.1 < ij.2 ∧ σ ij.2 < σ ij.1)).map embLLCC
  let F_LR := (Finset.univ.filter (fun ca : Fin k × Fin r =>
    ca.1 < R.unpaired ca.2 ∧ R.unpaired ca.2 < R.mate ca.1)).map embLR
  let F_RR := (Finset.univ.filter (fun ij : Fin k × Fin k =>
    ij.1 < ij.2 ∧ ij.2 < R.mate ij.1 ∧ R.mate ij.1 < R.mate ij.2)).map embRR
  have h_union : Finset.univ.filter pred =
      F_LL_int ∪ F_LL_open ∪ F_LL_cc ∪ F_LR ∪ F_RR := by
    ext xy
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun hp => ?_, fun h => ?_⟩
    · rcases xy with ⟨x, y⟩
      rcases hp with ⟨h1, h2, h3⟩
      rcases x with i₁ | t₁ <;> rcases y with i₂ | t₂
      · by_cases hm1 : L.mate i₁ = i₁ <;> by_cases hm2 : L.mate i₂ = i₂
        · refine Or.inl (Or.inl (Or.inr (Finset.mem_map.mpr ?_)))
          refine ⟨(L.unpairedIdx i₂ hm2, L.unpairedIdx i₁ hm1), ?_, ?_⟩
          · rw [Finset.mem_filter]
            dsimp [M, concatSumFun] at h1 h3
            rw [dif_pos hm1, dif_pos hm2] at h3
            rw [concatSlotEquiv_inl_lt_inl] at h1
            rw [concatSlotEquiv_inr_lt_inr] at h3
            have ha : L.unpairedIdx i₂ hm2 < L.unpairedIdx i₁ hm1 := by
              apply L.strictMono_unpaired.lt_iff_lt.mp
              rwa [L.unpaired_unpairedIdx, L.unpaired_unpairedIdx]
            exact ⟨Finset.mem_univ _, ha, R.strictMono_unpaired.lt_iff_lt.mp h3⟩
          · dsimp [embLLCC]
            rw [L.unpaired_unpairedIdx, L.unpaired_unpairedIdx]
        · exfalso
          dsimp [M, concatSumFun] at h3
          rw [dif_pos hm1, dif_neg hm2] at h3
          exact not_concatSlotEquiv_inr_lt_inl _ _ h3
        · refine Or.inl (Or.inl (Or.inl (Or.inr (Finset.mem_map.mpr ?_))))
          refine ⟨(L.mate i₁, L.unpairedIdx i₂ hm2), ?_, ?_⟩
          · rw [Finset.mem_filter]
            dsimp [M, concatSumFun] at h1 h2
            rw [dif_neg hm1] at h2
            rw [concatSlotEquiv_inl_lt_inl] at h1 h2
            rw [L.unpaired_unpairedIdx, L.mate_mate]
            exact ⟨Finset.mem_univ _, h2, h1⟩
          · dsimp [embLLOpen]
            rw [L.mate_mate, L.unpaired_unpairedIdx]
        · refine Or.inl (Or.inl (Or.inl (Or.inl (Finset.mem_map.mpr ?_))))
          refine ⟨(L.mate i₂, L.mate i₁), ?_, ?_⟩
          · rw [Finset.mem_filter]
            dsimp [M, concatSumFun] at h1 h2 h3
            rw [dif_neg hm1] at h2 h3
            rw [dif_neg hm2] at h3
            rw [concatSlotEquiv_inl_lt_inl] at h1 h2 h3
            rw [L.mate_mate, L.mate_mate]
            exact ⟨Finset.mem_univ _, h3, h2, h1⟩
          · dsimp [embLLInt]
            rw [L.mate_mate, L.mate_mate]
      · have hm1 : L.mate i₁ = i₁ := by
          dsimp [M, concatSumFun] at h2
          by_contra hne
          rw [dif_neg hne] at h2
          exact not_concatSlotEquiv_inr_lt_inl _ _ h2
        have hne2 : R.mate t₂ ≠ t₂ := by
          dsimp [M, concatSumFun] at h3
          rw [dif_pos hm1] at h3
          intro hfix2
          rw [dif_pos hfix2] at h3
          exact not_concatSlotEquiv_inr_lt_inl _ _ h3
        refine Or.inl (Or.inr (Finset.mem_map.mpr ?_))
        refine ⟨(t₂, σ (L.unpairedIdx i₁ hm1)), ?_, ?_⟩
        · rw [Finset.mem_filter]
          dsimp [M, concatSumFun] at h2 h3
          rw [dif_pos hm1] at h2 h3
          rw [dif_neg hne2] at h3
          rw [concatSlotEquiv_inr_lt_inr] at h2 h3
          exact ⟨Finset.mem_univ _, h2, h3⟩
        · dsimp [embLR]
          rw [σ.symm_apply_apply, L.unpaired_unpairedIdx]
      · exfalso
        exact not_concatSlotEquiv_inr_lt_inl t₁ i₂ h1
      · have hne1 : R.mate t₁ ≠ t₁ := by
          dsimp [M, concatSumFun] at h2
          intro hfix1
          rw [dif_pos hfix1] at h2
          exact not_concatSlotEquiv_inr_lt_inl _ _ h2
        have hne2 : R.mate t₂ ≠ t₂ := by
          dsimp [M, concatSumFun] at h3
          rw [dif_neg hne1] at h3
          intro hfix2
          rw [dif_pos hfix2] at h3
          exact not_concatSlotEquiv_inr_lt_inl _ _ h3
        refine Or.inr (Finset.mem_map.mpr ?_)
        refine ⟨(t₁, t₂), ?_, rfl⟩
        rw [Finset.mem_filter]
        dsimp [M, concatSumFun] at h1 h2 h3
        rw [dif_neg hne1] at h2 h3
        rw [dif_neg hne2] at h3
        rw [concatSlotEquiv_inr_lt_inr] at h1 h2 h3
        exact ⟨Finset.mem_univ _, h1, h2, h3⟩
    · rcases h with (((h1 | h2) | h3) | h4) | h5
      · rcases Finset.mem_map.mp h1 with ⟨⟨u, v⟩, huv, rfl⟩
        rw [Finset.mem_filter] at huv
        rcases huv with ⟨_, huv_lt, hv_lt, hmu_lt⟩
        have hne_u : L.mate (L.mate u) ≠ L.mate u := by
          rw [L.mate_mate]; exact ne_of_lt (huv_lt.trans hv_lt)
        have hne_v : L.mate (L.mate v) ≠ L.mate v := by
          rw [L.mate_mate]; exact ne_of_lt (hv_lt.trans hmu_lt)
        dsimp [pred, embLLInt, M, concatSumFun]
        rw [dif_neg hne_v, dif_neg hne_u, L.mate_mate, L.mate_mate]
        exact ⟨(concatSlotEquiv_inl_lt_inl _ _).mpr hmu_lt,
          (concatSlotEquiv_inl_lt_inl _ _).mpr hv_lt,
          (concatSlotEquiv_inl_lt_inl _ _).mpr huv_lt⟩
      · rcases Finset.mem_map.mp h2 with ⟨⟨u, a⟩, hua, rfl⟩
        rw [Finset.mem_filter] at hua
        rcases hua with ⟨_, hu_lt, ha_lt⟩
        have hne_u : L.mate (L.mate u) ≠ L.mate u := by
          rw [L.mate_mate]; exact ne_of_lt (hu_lt.trans ha_lt)
        dsimp [pred, embLLOpen, M, concatSumFun]
        rw [dif_neg hne_u, dif_pos (L.mate_unpaired a), L.mate_mate]
        exact ⟨(concatSlotEquiv_inl_lt_inl _ _).mpr ha_lt,
          (concatSlotEquiv_inl_lt_inl _ _).mpr hu_lt,
          concatSlotEquiv_inl_lt_inr _ _⟩
      · rcases Finset.mem_map.mp h3 with ⟨⟨a₁, a₂⟩, ha, rfl⟩
        rw [Finset.mem_filter] at ha
        rcases ha with ⟨_, ha_lt, hσ_lt⟩
        dsimp [pred, embLLCC, M, concatSumFun]
        rw [dif_pos (L.mate_unpaired a₂), dif_pos (L.mate_unpaired a₁),
            L.unpairedIdx_unpaired, L.unpairedIdx_unpaired]
        exact ⟨(concatSlotEquiv_inl_lt_inl _ _).mpr (L.strictMono_unpaired ha_lt),
          concatSlotEquiv_inl_lt_inr _ _,
          (concatSlotEquiv_inr_lt_inr _ _).mpr (R.strictMono_unpaired hσ_lt)⟩
      · rcases Finset.mem_map.mp h4 with ⟨⟨t, b⟩, htb, rfl⟩
        rw [Finset.mem_filter] at htb
        rcases htb with ⟨_, ht_lt, hb_lt⟩
        have hne_t : R.mate t ≠ t := (ne_of_lt (ht_lt.trans hb_lt)).symm
        dsimp [pred, embLR, M, concatSumFun]
        rw [dif_pos (L.mate_unpaired _), dif_neg hne_t,
            L.unpairedIdx_unpaired, σ.apply_symm_apply]
        exact ⟨concatSlotEquiv_inl_lt_inr _ _,
          (concatSlotEquiv_inr_lt_inr _ _).mpr ht_lt,
          (concatSlotEquiv_inr_lt_inr _ _).mpr hb_lt⟩
      · rcases Finset.mem_map.mp h5 with ⟨⟨t₁, t₂⟩, htt, rfl⟩
        rw [Finset.mem_filter] at htt
        rcases htt with ⟨_, h1, h2, h3⟩
        have hne1 : R.mate t₁ ≠ t₁ := (ne_of_lt (h1.trans h2)).symm
        have hne2 : R.mate t₂ ≠ t₂ := (ne_of_lt (h2.trans h3)).symm
        dsimp [pred, embRR, M, concatSumFun]
        rw [dif_neg hne1, dif_neg hne2]
        exact ⟨(concatSlotEquiv_inr_lt_inr _ _).mpr h1,
          (concatSlotEquiv_inr_lt_inr _ _).mpr h2,
          (concatSlotEquiv_inr_lt_inr _ _).mpr h3⟩
  have h_disj1 : Disjoint F_LL_int F_LL_open := by
    rw [Finset.disjoint_left]
    intro xy h1 h2
    rcases Finset.mem_map.mp h1 with ⟨⟨u, v⟩, huv, rfl⟩
    rcases Finset.mem_map.mp h2 with ⟨⟨w, a⟩, _, heq⟩
    rw [Finset.mem_filter] at huv
    rcases huv with ⟨_, huv1, huv2, _⟩
    dsimp only at huv1 huv2
    have hv_eq : L.unpaired a = L.mate u := Sum.inl.inj (Prod.mk.inj heq).2
    have hfix : L.mate (L.mate u) = L.mate u := by
      rw [← hv_eq, L.mate_unpaired]
    rw [L.mate_mate] at hfix
    exact (ne_of_lt (huv1.trans huv2)) hfix
  have h_disj2 : Disjoint (F_LL_int ∪ F_LL_open) F_LL_cc := by
    rw [Finset.disjoint_left]
    intro xy hleft h3
    rcases Finset.mem_map.mp h3 with ⟨⟨a₁, a₂⟩, _, rfl⟩
    rcases Finset.mem_union.mp hleft with h1 | h2
    · rcases Finset.mem_map.mp h1 with ⟨⟨u, v⟩, huv, heq⟩
      rw [Finset.mem_filter] at huv
      rcases huv with ⟨_, _, huv2, huv3⟩
      dsimp only at huv2 huv3
      have hv_eq : L.mate v = L.unpaired a₂ := Sum.inl.inj (Prod.mk.inj heq).1
      have hfix : L.mate (L.mate v) = L.mate v := by
        rw [hv_eq, L.mate_unpaired]
      rw [L.mate_mate] at hfix
      exact (ne_of_lt (huv2.trans huv3)) hfix
    · rcases Finset.mem_map.mp h2 with ⟨⟨u, a⟩, hua, heq⟩
      rw [Finset.mem_filter] at hua
      rcases hua with ⟨_, hua1, hua2⟩
      dsimp only at hua1 hua2
      have hu_eq : L.mate u = L.unpaired a₂ := Sum.inl.inj (Prod.mk.inj heq).1
      have hfix : L.mate (L.mate u) = L.mate u := by
        rw [hu_eq, L.mate_unpaired]
      rw [L.mate_mate] at hfix
      exact (ne_of_lt (hua1.trans hua2)) hfix
  have h_disj3 : Disjoint (F_LL_int ∪ F_LL_open ∪ F_LL_cc) F_LR := by
    rw [Finset.disjoint_left]
    intro xy hleft h4
    rcases Finset.mem_map.mp h4 with ⟨⟨t, b⟩, _, rfl⟩
    rcases Finset.mem_union.mp hleft with h12 | h3
    · rcases Finset.mem_union.mp h12 with h1 | h2
      · rcases Finset.mem_map.mp h1 with ⟨_, _, heq⟩
        exact Sum.inl_ne_inr (Prod.mk.inj heq).2
      · rcases Finset.mem_map.mp h2 with ⟨_, _, heq⟩
        exact Sum.inl_ne_inr (Prod.mk.inj heq).2
    · rcases Finset.mem_map.mp h3 with ⟨_, _, heq⟩
      exact Sum.inl_ne_inr (Prod.mk.inj heq).2
  have h_disj4 : Disjoint (F_LL_int ∪ F_LL_open ∪ F_LL_cc ∪ F_LR) F_RR := by
    rw [Finset.disjoint_left]
    intro xy hleft h5
    rcases Finset.mem_map.mp h5 with ⟨⟨t₁, t₂⟩, _, rfl⟩
    rcases Finset.mem_union.mp hleft with h123 | h4
    · rcases Finset.mem_union.mp h123 with h12 | h3
      · rcases Finset.mem_union.mp h12 with h1 | h2
        · rcases Finset.mem_map.mp h1 with ⟨_, _, heq⟩
          exact Sum.inl_ne_inr (Prod.mk.inj heq).1
        · rcases Finset.mem_map.mp h2 with ⟨_, _, heq⟩
          exact Sum.inl_ne_inr (Prod.mk.inj heq).1
      · rcases Finset.mem_map.mp h3 with ⟨_, _, heq⟩
        exact Sum.inl_ne_inr (Prod.mk.inj heq).1
    · rcases Finset.mem_map.mp h4 with ⟨_, _, heq⟩
      exact Sum.inl_ne_inr (Prod.mk.inj heq).1
  rw [h_pull, h_union, Finset.card_union_of_disjoint h_disj4,
      Finset.card_union_of_disjoint h_disj3, Finset.card_union_of_disjoint h_disj2,
      Finset.card_union_of_disjoint h_disj1]
  simp only [F_LL_int, F_LL_open, F_LL_cc, F_LR, F_RR, Finset.card_map]
  change L.internalCross + L.openCross + permInversions σ + R.openCross + R.internalCross =
    L.partialCross + R.partialCross + permInversions σ
  dsimp [partialCross]
  omega

end PartialPairing

end

end QFT
