import Mathlib

namespace PEqualNP.Outside.L_meta_961

variable {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
variable {w : Fin N} {T : Finset (Fin N)}
variable {q M r : ℕ}

-- Two distinct lines have at most one common point.

lemma share_le_one
    (hpair : ∀ p p2 l l2 : Fin N, p ≠ p2 → l ≠ l2 →
      ¬ (I p l ∧ I p l2 ∧ I p2 l ∧ I p2 l2)) (l : Fin N) (hl : l ≠ w) :
    (Finset.univ.filter (fun p : Fin N => I p l ∧ I p w)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  by_contra hab
  exact hpair a b l w hab hl ⟨ha.1, ha.2, hb.1, hb.2⟩

-- A line that is not `w` carries at least `r` points that are not on `w`.

lemma per_line_card
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p : Fin N => I p l)).card = q)
    (hshare : (Finset.univ.filter (fun p : Fin N => I p l ∧ I p w)).card ≤ 1)
    (hr : r + 1 = q) :
    r ≤ ((Finset.univ.filter (fun p : Fin N => I p l)).filter (fun p => ¬ I p w)).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun p : Fin N => I p l)) (p := fun p : Fin N => I p w)
  have hrewrite : (Finset.univ.filter (fun p : Fin N => I p l)).filter (fun p => I p w)
      = Finset.univ.filter (fun p : Fin N => I p l ∧ I p w) := by
    ext p
    simp [Finset.mem_filter, and_assoc]
  rw [hrewrite] at hsplit
  have hq : (Finset.univ.filter (fun p : Fin N => I p l)).card = q := hline l
  omega

end PEqualNP.Outside.L_meta_961

theorem PEqualNP.Outside.L_meta_961 :
    ∀ (N q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (w : Fin N) (T : Finset (Fin N)),
      (∀ p p2 l l2 : Fin N, p ≠ p2 → l ≠ l2 → ¬ (I p l ∧ I p l2 ∧ I p2 l ∧ I p2 l2)) →
        (∀ l3 : Fin N, (Finset.univ.filter (fun p3 : Fin N => I p3 l3)).card = q) →
          (∀ p4 : Fin N, (Finset.univ.filter (fun l4 : Fin N => I p4 l4)).card ≤ q) →
            ∀ (M r : ℕ), M + 1 + q * T.card = N → r + 1 = q →
              M * r ≤ (Finset.univ.filter (fun e : Fin N × Fin N =>
                I e.1 e.2 ∧ e.1 ∉ T ∧ ¬ I e.1 w ∧ e.2 ≠ w ∧ ¬ ∃ t ∈ T, I t e.2)).card := by
  classical
  intro N q I inst w T hpair hline hdeg M r hM hr
  set row : Fin N → Finset (Fin N) := fun l => Finset.univ.filter (fun p => I p l) with hrow
  set good : Finset (Fin N) := Finset.univ.filter (fun l => l ≠ w ∧ ¬ ∃ t ∈ T, I t l)
    with hgood
  set A : Fin N → Finset (Fin N) := fun l => (row l).filter (fun p => ¬ I p w) with hAdef
  set Prs : Finset (Fin N × Fin N) := Finset.univ.filter (fun e : Fin N × Fin N =>
    I e.1 e.2 ∧ e.1 ∉ T ∧ ¬ I e.1 w ∧ e.2 ≠ w ∧ ¬ ∃ t ∈ T, I t e.2) with hPrs
  -- lines that are bad: `w` itself, or a line through a point of `T`
  have hbad_sub : Finset.univ.filter (fun l : Fin N => ¬ (l ≠ w ∧ ¬ ∃ t ∈ T, I t l))
      ⊆ insert w (T.biUnion (fun t => Finset.univ.filter (fun l : Fin N => I t l))) := by
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    by_cases hlw : l = w
    · simp [hlw]
    · have hex : ∃ t ∈ T, I t l := by
        by_contra hcon
        exact hl ⟨hlw, hcon⟩
      obtain ⟨t, htT, htl⟩ := hex
      simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact Or.inr ⟨t, htT, htl⟩
  have hbad_card : (Finset.univ.filter (fun l : Fin N => ¬ (l ≠ w ∧ ¬ ∃ t ∈ T, I t l))).card
      ≤ 1 + q * T.card := by
    have h1 : (Finset.univ.filter (fun l : Fin N => ¬ (l ≠ w ∧ ¬ ∃ t ∈ T, I t l))).card
        ≤ (insert w (T.biUnion (fun t => Finset.univ.filter (fun l : Fin N => I t l)))).card :=
      Finset.card_le_card hbad_sub
    have h2 : (insert w (T.biUnion (fun t => Finset.univ.filter (fun l : Fin N => I t l)))).card
        ≤ (T.biUnion (fun t => Finset.univ.filter (fun l : Fin N => I t l))).card + 1 :=
      Finset.card_insert_le _ _
    have h3 : (T.biUnion (fun t => Finset.univ.filter (fun l : Fin N => I t l))).card
        ≤ ∑ t ∈ T, (Finset.univ.filter (fun l : Fin N => I t l)).card :=
      Finset.card_biUnion_le
    have h4 : ∑ t ∈ T, (Finset.univ.filter (fun l : Fin N => I t l)).card ≤ T.card * q := by
      have hs : ∑ t ∈ T, (Finset.univ.filter (fun l : Fin N => I t l)).card ≤ ∑ t ∈ T, q :=
        Finset.sum_le_sum (fun t _ => hdeg t)
      rw [Finset.sum_const] at hs
      simpa [nsmul_eq_mul] using hs
    have h5 : T.card * q = q * T.card := Nat.mul_comm _ _
    omega
  have hgood_card : M ≤ good.card := by
    have hcompl := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin N))) (p := fun l : Fin N => l ≠ w ∧ ¬ ∃ t ∈ T, I t l)
    rw [← hgood] at hcompl
    simp only [Finset.card_univ, Fintype.card_fin] at hcompl
    omega
  have hA_ge : ∀ l ∈ good, r ≤ (A l).card := by
    intro l hl
    have hlw : l ≠ w ∧ ¬ ∃ t ∈ T, I t l := by
      rw [hgood] at hl
      simpa using hl
    have hsh : (Finset.univ.filter (fun p : Fin N => I p l ∧ I p w)).card ≤ 1 :=
      PEqualNP.Outside.L_meta_961.share_le_one (I := I) (w := w) hpair l hlw.1
    have := PEqualNP.Outside.L_meta_961.per_line_card (I := I) (w := w) (q := q) (r := r)
      (hline := hline) (hshare := hsh) (hr := hr)
    simpa [hAdef, hrow] using this
  have himage : ∀ l : Fin N,
      ((A l).image (fun p : Fin N => (p, l))).card = (A l).card := by
    intro l
    refine Finset.card_image_of_injOn ?_
    intro x _ y _ hxy
    exact Prod.mk.injEq x l y l |>.mp hxy |>.1
  have hdisj : ∀ l ∈ good, ∀ l' ∈ good, l ≠ l' →
      Disjoint ((A l).image (fun p : Fin N => (p, l)))
        ((A l').image (fun p : Fin N => (p, l'))) := by
    intro l _ l' _ hne
    rw [Finset.disjoint_left]
    intro e he he'
    simp only [Finset.mem_image] at he he'
    obtain ⟨p, _, hp⟩ := he
    obtain ⟨p', _, hp'⟩ := he'
    have hpp : (p, l) = (p', l') := hp.trans hp'.symm
    exact hne ((Prod.mk.injEq p l p' l').mp hpp).2
  have hsub : good.biUnion (fun l => (A l).image (fun p : Fin N => (p, l))) ⊆ Prs := by
    intro e he
    simp only [Finset.mem_biUnion, Finset.mem_image] at he
    obtain ⟨l, hlgood, p, hp, rfl⟩ := he
    simp only [hgood, Finset.mem_filter, Finset.mem_univ, true_and] at hlgood
    have hprow : p ∈ row l := (Finset.mem_filter.mp hp).1
    have hpnw : ¬ I p w := (Finset.mem_filter.mp hp).2
    have hpI : I p l := by simpa [hrow] using hprow
    have hpnT : p ∉ T := by
      intro hpT
      exact hlgood.2 ⟨p, hpT, hpI⟩
    simp only [hPrs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hpI, hpnT, hpnw, hlgood.1, hlgood.2⟩
  have hbcard : (good.biUnion (fun l => (A l).image (fun p : Fin N => (p, l)))).card
      = ∑ l ∈ good, (A l).card := by
    rw [Finset.card_biUnion hdisj]
    exact Finset.sum_congr rfl (fun l _ => himage l)
  calc M * r ≤ good.card * r := Nat.mul_le_mul_right r hgood_card
    _ = ∑ l ∈ good, r := by
      rw [Finset.sum_const]
      simp [nsmul_eq_mul]
    _ ≤ ∑ l ∈ good, (A l).card := Finset.sum_le_sum hA_ge
    _ = (good.biUnion (fun l => (A l).image (fun p : Fin N => (p, l)))).card := hbcard.symm
    _ ≤ Prs.card := Finset.card_le_card hsub
