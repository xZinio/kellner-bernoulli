import KellnerBernoulli.Counting
import KellnerBernoulli.Data

/-!
# The finite range

A kernel-checked computation (`decide +kernel`, no `native_decide`): every `n` with
`2015 ≤ n < (4 * 10 ^ 6) ^ 2` has at least three good primes.
-/

namespace KellnerBernoulli

/-- The primes `p > √n` with `p ≤ ⌊n / p⌋ + (n mod p)`, i.e. with base-`p` digit sum at least `p`. -/
def goodPrimes (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun p => p.Prime ∧ n < p * p ∧ p ≤ n / p + n % p)

theorem mem_goodPrimes {n p : ℕ} :
    p ∈ goodPrimes n ↔ p.Prime ∧ n < p * p ∧ p ≤ n / p + n % p := by
  unfold goodPrimes
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  by_contra hcon
  have hlt : n < p := by omega
  have h2 := h.2.2
  rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt] at h2
  omega

/-- Strictly increasing lists. -/
def incr : List ℕ → Bool
  | [] => true
  | a :: l => (match l with | [] => true | b :: _ => Nat.blt a b) && incr l

theorem pairwise_of_incr {l : List ℕ} (h : incr l = true) : l.Pairwise (· < ·) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a l ih =>
    unfold incr at h
    rw [Bool.and_eq_true] at h
    have hl := ih h.2
    refine List.Pairwise.cons ?_ hl
    cases l with
    | nil => simp
    | cons b l =>
      have hab : a < b := by simpa using h.1
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hab
      · exact hab.trans ((List.pairwise_cons.mp hl).1 x hx)

/-! ## Primality by trial division -/

/-- `List.all`, written with `List.rec` (much faster in the kernel than structural recursion). -/
def allR (f : ℕ → Bool) (l : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => f a && ih) l

theorem allR_eq_true {f : ℕ → Bool} {l : List ℕ} : allR f l = true ↔ ∀ x ∈ l, f x = true := by
  induction l with
  | nil => simp [allR]
  | cons a l ih =>
    change (f a && allR f l) = true ↔ _
    rw [Bool.and_eq_true, ih]
    simp

/-- Trial division by the primes `q` of the list with `q ^ 2 ≤ p`; the list must be increasing. -/
def trialOK (p : ℕ) (l : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun q _ ih => Nat.blt p (q * q) || (!(Nat.beq (p % q) 0) && ih)) l

theorem trialOK_sound {p : ℕ} : ∀ {l : List ℕ}, l.Pairwise (· < ·) → trialOK p l = true →
    ∀ q ∈ l, q * q ≤ p → p % q ≠ 0 := by
  intro l
  induction l with
  | nil => simp
  | cons q0 l ih =>
    intro hpw h q hq hqq
    change (Nat.blt p (q0 * q0) || (!(Nat.beq (p % q0) 0) && trialOK p l)) = true at h
    rw [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at h
    have hpw' := List.pairwise_cons.mp hpw
    rcases h with h | ⟨h1, h2⟩
    · exfalso
      rcases List.mem_cons.mp hq with rfl | hq'
      · omega
      · have := hpw'.1 q hq'
        nlinarith
    · rcases List.mem_cons.mp hq with rfl | hq'
      · exact Nat.ne_of_beq_eq_false h1
      · exact ih hpw'.2 h2 q hq' hqq

/-- Trial division by the primes below `2030`. -/
def isPrime (p : ℕ) : Bool :=
  Nat.blt 1 p && Nat.blt p (2030 * 2030) && trialOK p Data.trial

/-- Every `m` with `2 ≤ m < 2030` is in the list or has a proper divisor in the list. -/
def trialComplete : Bool :=
  (List.range 2030).all (fun m => Nat.blt m 2 ||
    Data.trial.any (fun r => Nat.beq r m || (Nat.blt 1 r && Nat.blt r m && Nat.beq (m % r) 0)))

theorem trialComplete_true : trialComplete = true := by decide +kernel

theorem mem_trial {q : ℕ} (hq : q.Prime) (hlt : q < 2030) : q ∈ Data.trial := by
  have h := trialComplete_true
  unfold trialComplete at h
  rw [List.all_eq_true] at h
  have hq' := h q (List.mem_range.mpr hlt)
  simp only [Bool.or_eq_true, Nat.blt_eq, List.any_eq_true, Nat.beq_eq,
    Bool.and_eq_true] at hq'
  rcases hq' with h2 | ⟨r, hr, h3⟩
  · exact absurd hq.two_le (by omega)
  · rcases h3 with rfl | ⟨⟨h1, h4⟩, h5⟩
    · exact hr
    · exfalso
      rcases (Nat.dvd_prime hq).mp (Nat.dvd_of_mod_eq_zero h5) with h6 | h6 <;> omega

theorem prime_of_isPrime (htr : Data.trial.Pairwise (· < ·)) {p : ℕ} (h : isPrime p = true) :
    p.Prime := by
  unfold isPrime at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  by_contra hnp
  have hm : p.minFac.Prime := Nat.minFac_prime (by omega)
  have hsq : p.minFac * p.minFac ≤ p := by
    have := Nat.minFac_sq_le_self (by omega) hnp
    nlinarith
  have hlt : p.minFac < 2030 := by
    by_contra hcon
    have : 2030 ≤ p.minFac := by omega
    nlinarith
  exact trialOK_sound htr h3 _ (mem_trial hm hlt) hsq
    (Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd p))

/-! ## The chain: `2015 ≤ n < 10 ^ 8` -/

/-- Looks for `k` primes of the list that are good for `n`; returns the smallest `(⌊n/p⌋ + 1) p`. -/
def reach (n : ℕ) : ℕ → ℕ → List ℕ → ℕ
  | 0, m, _ => m
  | _ + 1, _, [] => 0
  | k + 1, m, p :: ps =>
    bif Nat.blt n (p * p) && Nat.ble p (n / p + n % p) then
      reach n k (bif Nat.blt m ((n / p + 1) * p) then m else (n / p + 1) * p) ps
    else reach n (k + 1) m ps

theorem good_of_le {n m p : ℕ} (hpos : 0 < p) (h1 : n < p * p) (h2 : p ≤ n / p + n % p)
    (hnm : n ≤ m) (hm : m < (n / p + 1) * p) : m < p * p ∧ p ≤ m / p + m % p := by
  have hq : n / p < p := Nat.div_lt_of_lt_mul h1
  have hdm := Nat.div_add_mod n p
  have hmod := Nat.mod_lt n hpos
  have hdiv : m / p = n / p := by
    apply Nat.div_eq_of_lt_le
    · calc n / p * p ≤ n := Nat.div_mul_le_self n p
        _ ≤ m := hnm
    · exact hm
  have hdm' := Nat.div_add_mod m p
  rw [hdiv] at hdm'
  refine ⟨?_, ?_⟩
  · calc m < (n / p + 1) * p := hm
      _ ≤ p * p := Nat.mul_le_mul_right _ hq
  · rw [hdiv]; omega

theorem reach_sound {n : ℕ} : ∀ (ps : List ℕ) (k m r : ℕ), reach n k m ps = r → n < r →
    ps.Pairwise (· < ·) →
    ∃ F : Finset ℕ, F.card = k ∧ r ≤ m ∧
      ∀ p ∈ F, p ∈ ps ∧ n < p * p ∧ p ≤ n / p + n % p ∧ r ≤ (n / p + 1) * p := by
  intro ps
  induction ps with
  | nil =>
    intro k m r hr hn _
    cases k with
    | zero =>
      simp only [reach] at hr
      exact ⟨∅, rfl, by omega, by simp⟩
    | succ k =>
      simp only [reach] at hr
      omega
  | cons p ps ih =>
    intro k m r hr hn hpw
    have hpw' := (List.pairwise_cons.mp hpw)
    cases k with
    | zero =>
      simp only [reach] at hr
      exact ⟨∅, rfl, by omega, by simp⟩
    | succ k =>
      rw [reach] at hr
      by_cases hc : (Nat.blt n (p * p) && Nat.ble p (n / p + n % p)) = true
      · rw [hc, Bool.cond_true] at hr
        obtain ⟨F, hF1, hF2, hF3⟩ := ih k _ r hr hn hpw'.2
        simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hc
        have hpF : p ∉ F := fun hmem => absurd (hpw'.1 p (hF3 p hmem).1) (lt_irrefl p)
        have hm : r ≤ m ∧ r ≤ (n / p + 1) * p := by
          by_cases hb : Nat.blt m ((n / p + 1) * p) = true
          · rw [hb, Bool.cond_true] at hF2
            rw [Nat.blt_eq] at hb
            omega
          · rw [Bool.not_eq_true] at hb
            rw [hb, Bool.cond_false] at hF2
            have : ¬ m < (n / p + 1) * p := by
              intro hlt
              rw [← Nat.blt_eq] at hlt
              rw [hb] at hlt
              exact Bool.noConfusion hlt
            omega
        refine ⟨insert p F, ?_, hm.1, ?_⟩
        · rw [Finset.card_insert_of_notMem hpF, hF1]
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact ⟨List.mem_cons_self, hc.1, hc.2, hm.2⟩
          · obtain ⟨h1, h2⟩ := hF3 x hx
            exact ⟨List.mem_cons_of_mem _ h1, h2⟩
      · rw [Bool.not_eq_true] at hc
        rw [hc, Bool.cond_false] at hr
        obtain ⟨F, hF1, hF2, hF3⟩ := ih (k + 1) m r hr hn hpw'.2
        refine ⟨F, hF1, hF2, fun x hx => ?_⟩
        obtain ⟨h1, h2⟩ := hF3 x hx
        exact ⟨List.mem_cons_of_mem _ h1, h2⟩

/-- Every `m` with `n ≤ m < hi` has three good primes in the list. -/
def loop (hi : ℕ) : ℕ → ℕ → List ℕ → Bool
  | 0, _, _ => false
  | f + 1, n, ps =>
    bif Nat.ble hi n then true else
      match ps.dropWhile (fun p => Nat.ble (p * p) n) with
      | [] => false
      | q :: qs =>
        match reach n 3 1000000000 (q :: qs) with
        | 0 => false
        | r + 1 => Nat.blt n (r + 1) && loop hi f (r + 1) (q :: qs)

theorem loop_sound {hi : ℕ} : ∀ (f n : ℕ) (ps : List ℕ), loop hi f n ps = true →
    ps.Pairwise (· < ·) → (∀ p ∈ ps, p.Prime) →
    ∀ m, n ≤ m → m < hi → 3 ≤ (goodPrimes m).card := by
  intro f
  induction f with
  | zero => intro n ps h; simp [loop] at h
  | succ f ih =>
    intro n ps h hpw hpr m hnm hm
    rw [loop] at h
    by_cases hhi : Nat.ble hi n = true
    · rw [Nat.ble_eq] at hhi; omega
    · rw [Bool.not_eq_true] at hhi
      rw [hhi, Bool.cond_false] at h
      have hsub : (ps.dropWhile (fun p => Nat.ble (p * p) n)).Sublist ps :=
        (List.dropWhile_suffix _).sublist
      split at h
      · exact Bool.noConfusion h
      · rename_i q qs heq
        rw [heq] at hsub
        have hpw' := hpw.sublist hsub
        have hpr' : ∀ p ∈ q :: qs, p.Prime := fun p hp => hpr p (hsub.subset hp)
        split at h
        · exact Bool.noConfusion h
        · rename_i r hr
          rw [Bool.and_eq_true, Nat.blt_eq] at h
          rcases Nat.lt_or_ge m (r + 1) with hlt | hge
          · obtain ⟨F, hF1, _, hF3⟩ := reach_sound (q :: qs) 3 _ (r + 1) hr h.1 hpw'
            rw [← hF1]
            apply Finset.card_le_card
            intro p hp
            obtain ⟨h1, h2, h3, h4⟩ := hF3 p hp
            have hpp := hpr' p h1
            rw [mem_goodPrimes]
            exact ⟨hpp, good_of_le hpp.pos h2 h3 hnm (lt_of_lt_of_le hlt h4)⟩
          · exact ih (r + 1) (q :: qs) h.2 hpw' hpr' m hge hm

/-! ## Windows: `9973 ≤ s < 4 * 10 ^ 6` -/

/-- For every `s` between the first element of the list and `hi`: the next `16` elements of the list
lie in an interval `(s, e]` with `(e - s) ^ 2 < 4 e`. -/
def cover (hi : ℕ) : List ℕ → Bool
  | [] => false
  | r :: rs =>
    match rs with
    | [] => false
    | r' :: _ =>
      match rs.drop 15 with
      | [] => false
      | e :: _ => Nat.blt ((e - r) * (e - r)) (4 * e) && (Nat.ble hi r' || cover hi rs)

/-- What the windows provide. -/
def HasWindow (s : ℕ) : Prop :=
  ∃ (T : Finset ℕ) (U : ℕ), 1 ≤ U ∧ T.card = 16 ∧
    (∀ p ∈ T, p.Prime ∧ s < p ∧ p ≤ s + U) ∧ U * U < 4 * (s + U)

theorem cover_sound {hi : ℕ} : ∀ l : List ℕ, cover hi l = true → l.Pairwise (· < ·) →
    (∀ p ∈ l, p.Prime) → ∀ s, (∃ r ∈ l.head?, r ≤ s) → s < hi → HasWindow s := by
  intro l
  induction l with
  | nil => intro h; simp [cover] at h
  | cons r rs ih =>
    intro h hpw hpr s hs hhi
    rw [cover.eq_def] at h
    simp only at h
    obtain ⟨r0, hr0, hrs⟩ := hs
    have hr0' : r0 = r := by simpa using hr0.symm
    subst hr0'
    cases rs with
    | nil => simp at h
    | cons r' rs' =>
      simp only at h
      split at h
      · exact Bool.noConfusion h
      · rename_i e es heq
        rw [Bool.and_eq_true, Nat.blt_eq, Bool.or_eq_true, Nat.ble_eq] at h
        have hpw' := List.pairwise_cons.mp hpw
        have hpr' : ∀ p ∈ r' :: rs', p.Prime := fun p hp => hpr p (List.mem_cons_of_mem _ hp)
        rcases Nat.lt_or_ge s r' with hlt | hge
        · -- the window `r' :: rs'` up to `e`
          set L := (r' :: rs').take 16 with hL
          have hlen : 15 < (r' :: rs').length := by
            by_contra hcon
            rw [List.drop_eq_nil_of_le (by omega)] at heq
            exact absurd heq (by simp)
          have hLlen : L.length = 16 := by rw [hL, List.length_take]; omega
          have hLpw : L.Pairwise (· < ·) := hpw'.2.sublist (List.take_sublist _ _)
          have hLnodup : L.Nodup := hLpw.imp (fun h => Nat.ne_of_lt h)
          have he : (r' :: rs')[15]'hlen = e := by
            have h1 : ((r' :: rs').drop 15)[0]? = some e := by rw [heq]; rfl
            rw [List.getElem?_drop] at h1
            simpa [List.getElem?_eq_getElem hlen] using h1
          have hmem : ∀ p ∈ L, p.Prime ∧ s < p ∧ p ≤ e := by
            intro p hp
            have hp' : p ∈ r' :: rs' := (List.take_sublist 16 _).subset hp
            refine ⟨hpr' p hp', ?_, ?_⟩
            · rcases List.mem_cons.mp hp' with rfl | h2
              · exact hlt
              · exact hlt.trans ((List.pairwise_cons.mp hpw'.2).1 p h2)
            · obtain ⟨i, hi1, hi2⟩ := List.getElem_of_mem hp
              have hi16 : i < 16 := by omega
              have hi3 : (r' :: rs')[i]'(by omega) = p := by
                have h4 : (List.take 16 (r' :: rs'))[i]'hi1 = p := hi2
                rwa [List.getElem_take] at h4
              rw [← hi3, ← he]
              rcases Nat.lt_or_ge i 15 with h15 | h15
              · exact le_of_lt (List.pairwise_iff_getElem.mp hpw'.2 i 15 (by omega) hlen h15)
              · have : i = 15 := by omega
                subst this; exact le_rfl
          have hse : s < e := by
            have h0 : e ∈ L := by
              rw [← he, hL]
              rw [List.mem_take_iff_getElem]
              exact ⟨15, by omega, rfl⟩
            exact (hmem e h0).2.1
          refine ⟨L.toFinset, e - s, by omega, ?_, ?_, ?_⟩
          · rw [List.toFinset_card_of_nodup hLnodup, hLlen]
          · intro p hp
            obtain ⟨h1, h2, h3⟩ := hmem p (List.mem_toFinset.mp hp)
            exact ⟨h1, h2, by omega⟩
          · have h1 : e - s ≤ e - r0 := by omega
            have h2 : (e - s) * (e - s) ≤ (e - r0) * (e - r0) := Nat.mul_le_mul h1 h1
            have h3 : s + (e - s) = e := by omega
            rw [h3]; omega
        · rcases h.2 with h2 | h2
          · omega
          · exact ih h2 hpw'.2 hpr' s ⟨r', by simp, hge⟩ hhi

/-- Consecutive blocks fit together and reach `4 * 10 ^ 6`. -/
def coverAll : List (List ℕ) → Bool
  | [] => false
  | [b] => cover 4000000 b
  | b :: b' :: bs => cover (b'.headD 0) b && coverAll (b' :: bs)

theorem coverAll_sound : ∀ L : List (List ℕ), coverAll L = true →
    (∀ b ∈ L, b.Pairwise (· < ·)) → (∀ b ∈ L, ∀ p ∈ b, p.Prime) →
    ∀ s, (∃ b ∈ L.head?, ∃ r ∈ b.head?, r ≤ s) → s < 4000000 → HasWindow s := by
  intro L
  induction L with
  | nil => intro h; simp [coverAll] at h
  | cons b L ih =>
    intro h hpw hpr s hs hlt
    obtain ⟨b0, hb0, hs⟩ := hs
    have hb0' : b0 = b := by simpa using hb0.symm
    subst hb0'
    cases L with
    | nil =>
      change cover 4000000 b0 = true at h
      exact cover_sound b0 h (hpw b0 (by simp)) (hpr b0 (by simp)) s hs hlt
    | cons b' bs =>
      change (cover (b'.headD 0) b0 && coverAll (b' :: bs)) = true at h
      rw [Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      cases b' with
      | nil =>
        exfalso
        cases bs with
        | nil => exact Bool.noConfusion h2
        | cons c cs =>
          change (cover (c.headD 0) [] && coverAll (c :: cs)) = true at h2
          rw [Bool.and_eq_true] at h2
          exact Bool.noConfusion h2.1
      | cons x xs =>
        change cover x b0 = true at h1
        rcases Nat.lt_or_ge s x with hsx | hsx
        · exact cover_sound b0 h1 (hpw b0 (by simp)) (hpr b0 (by simp)) s hs hsx
        · refine ih h2 (fun b hb => hpw b (List.mem_cons_of_mem _ hb))
            (fun b hb => hpr b (List.mem_cons_of_mem _ hb)) s ⟨x :: xs, by simp, x, by simp, hsx⟩ hlt

end KellnerBernoulli
