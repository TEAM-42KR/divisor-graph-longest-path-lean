import Mathlib
import RuleHRelease.Definitions.Foundation
set_option autoImplicit false
open DivisorGraphRuleH

theorem DivisorGraphRuleH.Arithmetic.consecutiveOddPrimes_lt_two_mul (qPrev q : ℕ) (h : DivisorGraphRuleH.ConsecutiveOddPrimes qPrev q) : q < 2 * qPrev := by
  rcases h with ⟨hp, hpodd, hq, hqodd, hpq, hnext⟩
  obtain ⟨r, hr, hpr, hrle⟩ := Nat.exists_prime_lt_and_le_two_mul qPrev hp.ne_zero
  have hr_ne_two : r ≠ 2 := by
    have hp2 := hp.two_le
    omega
  have hqr : q ≤ r := hnext r hr (hr.odd_of_ne_two hr_ne_two) hpr
  have hle : q ≤ 2 * qPrev := hqr.trans hrle
  have hne : q ≠ 2 * qPrev := by
    intro heq
    exact hqodd.not_two_dvd_nat ⟨qPrev, heq⟩
  omega


theorem DivisorGraphRuleH.Arithmetic.type3_pow_step (i : ℕ) (hi : 2 ≤ i) : (2 : ℕ) ^ i = 2 * 2 ^ (i - 1) := by
  calc
    (2 : ℕ) ^ i = 2 ^ ((i - 1) + 1) :=
      congrArg (fun n : ℕ => (2 : ℕ) ^ n) (by omega)
    _ = 2 * 2 ^ (i - 1) := by rw [pow_succ, Nat.mul_comm]


theorem DivisorGraphRuleH.Arithmetic.type2_aprime_lt_a (qPrev q d : ℕ) (hv : (DivisorGraphRuleH.Slot.type2 qPrev q d).Valid) :
    (DivisorGraphRuleH.Slot.type2 qPrev q d).a' < (DivisorGraphRuleH.Slot.type2 qPrev q d).a := by
  have hd : 0 < d := hv.1.pos
  have hq := Arithmetic.consecutiveOddPrimes_lt_two_mul qPrev q hv.2
  exact Nat.mul_lt_mul_of_pos_right hq hd


theorem DivisorGraphRuleH.Arithmetic.type3_a_eq_two_aprime (i d : ℕ) (hv : (DivisorGraphRuleH.Slot.type3 i d).Valid) :
    (DivisorGraphRuleH.Slot.type3 i d).a = 2 * (DivisorGraphRuleH.Slot.type3 i d).a' := by
  change 2 ^ i * d = 2 * (2 ^ (i - 1) * d)
  rw [Arithmetic.type3_pow_step i hv.2, Nat.mul_assoc]


theorem DivisorGraphRuleH.Arithmetic.slot_arithmetic (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) :
    0 < slot.a ∧ 2 ≤ slot.a' ∧ slot.a ≠ 2 ∧
    (slot.a = 1 ↔ slot = DivisorGraphRuleH.Slot.type1 1) ∧
    slot.a ≠ slot.a' ∧ slot.a ≤ slot.size ∧ slot.a' ≤ slot.size := by
  cases slot with
  | type1 d =>
    change Odd d at hv
    have hd : 0 < d := hv.pos
    have hd2 : d ≠ 2 := by
      intro heq
      subst d
      norm_num at hv
    have h1 : d = 1 ↔ Slot.type1 d = Slot.type1 1 := by
      constructor
      · intro heq; exact congrArg Slot.type1 heq
      · exact Slot.type1.inj
    change 0 < d ∧ 2 ≤ 3 * d ∧ d ≠ 2 ∧
      (d = 1 ↔ Slot.type1 d = Slot.type1 1) ∧
      d ≠ 3 * d ∧ d ≤ 3 * d ∧ 3 * d ≤ 3 * d
    exact ⟨hd, by omega, hd2, h1, by omega, by omega, le_rfl⟩
  | type2 qPrev q d =>
    have hv0 := hv
    change Odd d ∧ ConsecutiveOddPrimes qPrev q at hv
    have hd : 0 < d := hv.1.pos
    rcases hv.2 with ⟨hp, hpodd, hq, hqodd, hpq, hnext⟩
    have hq2 : 2 ≤ q := hq.two_le
    have hb : 2 ≤ q * d := by nlinarith
    have hlt : q * d < 2 * qPrev * d := Arithmetic.type2_aprime_lt_a qPrev q d hv0
    have h1 : 2 * qPrev * d = 1 ↔ Slot.type2 qPrev q d = Slot.type1 1 := by
      constructor
      · intro heq; omega
      · intro heq; cases heq
    change 0 < 2 * qPrev * d ∧ 2 ≤ q * d ∧ 2 * qPrev * d ≠ 2 ∧
      (2 * qPrev * d = 1 ↔ Slot.type2 qPrev q d = Slot.type1 1) ∧
      2 * qPrev * d ≠ q * d ∧ 2 * qPrev * d ≤ 2 * qPrev * d ∧ q * d ≤ 2 * qPrev * d
    exact ⟨by omega, hb, by omega, h1, by omega, le_rfl, by omega⟩
  | type3 i d =>
    have hv0 := hv
    change Odd d ∧ 2 ≤ i at hv
    have hd : 0 < d := hv.1.pos
    have hp : 2 ≤ (2 : ℕ) ^ (i - 1) := by
      calc
        2 = (2 : ℕ) ^ 1 := by norm_num
        _ ≤ (2 : ℕ) ^ (i - 1) := pow_le_pow_right₀ (by decide) (by omega)
    have hb : 2 ≤ 2 ^ (i - 1) * d := by nlinarith
    have heq : 2 ^ i * d = 2 * (2 ^ (i - 1) * d) := Arithmetic.type3_a_eq_two_aprime i d hv0
    have h1 : 2 ^ i * d = 1 ↔ Slot.type3 i d = Slot.type1 1 := by
      constructor
      · intro h; omega
      · intro h; cases h
    change 0 < 2 ^ i * d ∧ 2 ≤ 2 ^ (i - 1) * d ∧ 2 ^ i * d ≠ 2 ∧
      (2 ^ i * d = 1 ↔ Slot.type3 i d = Slot.type1 1) ∧
      2 ^ i * d ≠ 2 ^ (i - 1) * d ∧ 2 ^ i * d ≤ 2 ^ i * d ∧
      2 ^ (i - 1) * d ≤ 2 ^ i * d
    exact ⟨by omega, hb, by omega, h1, by omega, le_rfl, by omega⟩


theorem DivisorGraphRuleH.Arithmetic.a_pos (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) : 0 < slot.a := by
  exact (Arithmetic.slot_arithmetic slot hv).1


theorem DivisorGraphRuleH.Arithmetic.aprime_pos (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) : 0 < slot.a' := by
  have h := (Arithmetic.slot_arithmetic slot hv).2.1
  omega


theorem DivisorGraphRuleH.Arithmetic.two_le_aprime (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) : 2 ≤ slot.a' := by
  exact (Arithmetic.slot_arithmetic slot hv).2.1


theorem DivisorGraphRuleH.Arithmetic.a_ne_aprime (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) : slot.a ≠ slot.a' := by
  exact (Arithmetic.slot_arithmetic slot hv).2.2.2.2.1


theorem DivisorGraphRuleH.Arithmetic.a_ne_two (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) : slot.a ≠ 2 := by
  exact (Arithmetic.slot_arithmetic slot hv).2.2.1


theorem DivisorGraphRuleH.Arithmetic.a_eq_one_iff (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) : slot.a = 1 ↔ slot = DivisorGraphRuleH.Slot.type1 1 := by
  exact (Arithmetic.slot_arithmetic slot hv).2.2.2.1


theorem DivisorGraphRuleH.Arithmetic.a_le_size (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) : slot.a ≤ slot.size := by
  exact (Arithmetic.slot_arithmetic slot hv).2.2.2.2.2.1


theorem DivisorGraphRuleH.Arithmetic.aprime_le_size (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) : slot.a' ≤ slot.size := by
  exact (Arithmetic.slot_arithmetic slot hv).2.2.2.2.2.2


theorem DivisorGraphRuleH.Arithmetic.a_eq_one_moduli (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) : slot.a = 1 → slot.a' = 3 ∧ slot.beta = 2 ∧ slot.size = 3 := by
  intro ha
  have hs := (Arithmetic.a_eq_one_iff slot hv).mp ha
  subst slot
  norm_num [Slot.a', Slot.beta, Slot.size]


theorem DivisorGraphRuleH.Arithmetic.even_a_aprime_lt (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) : Even slot.a → slot.a' < slot.a := by
  intro he
  cases slot with
  | type1 d =>
    change Odd d at hv
    change Even d at he
    exact False.elim ((Nat.not_even_iff_odd.mpr hv) he)
  | type2 qPrev q d => exact Arithmetic.type2_aprime_lt_a qPrev q d hv
  | type3 i d =>
    have h := Arithmetic.type3_a_eq_two_aprime i d hv
    have hp := Arithmetic.aprime_pos (Slot.type3 i d) hv
    omega


theorem DivisorGraphRuleH.Arithmetic.even_a_not_dvd_aprime (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) : Even slot.a → ¬ slot.a ∣ slot.a' := by
  intro he hdiv
  have hlt := Arithmetic.even_a_aprime_lt slot hv he
  have hle := Nat.le_of_dvd (Arithmetic.aprime_pos slot hv) hdiv
  omega


theorem DivisorGraphRuleH.Arithmetic.even_a_lcm (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) : Even slot.a → Nat.lcm 2 slot.a = slot.a := by
  intro he
  exact Nat.lcm_eq_right he.two_dvd


theorem DivisorGraphRuleH.Arithmetic.even_a_link_ne_aprime (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) : Even slot.a → ∀ x : ℕ, slot.a ∣ x → x ≠ slot.a' := by
  intro he x hx heq
  exact Arithmetic.even_a_not_dvd_aprime slot hv he (heq ▸ hx)


theorem DivisorGraphRuleH.Arithmetic.odd_a_type1 (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) : Odd slot.a → ∃ d : ℕ, Odd d ∧ slot = DivisorGraphRuleH.Slot.type1 d := by
  intro ha
  cases slot with
  | type1 d => exact ⟨d, hv, rfl⟩
  | type2 qPrev q d =>
    change Odd (2 * qPrev * d) at ha
    exact False.elim (ha.not_two_dvd_nat ⟨qPrev * d, by simp only [Nat.mul_assoc]⟩)
  | type3 i d =>
    have heq := Arithmetic.type3_a_eq_two_aprime i d hv
    exact False.elim (ha.not_two_dvd_nat ⟨(Slot.type3 i d).a', heq⟩)


theorem DivisorGraphRuleH.Arithmetic.odd_a_moduli (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) : Odd slot.a →
    slot.a' = 3 * slot.a ∧ 2 * slot.a < slot.a' ∧
    2 * slot.a ≤ slot.size ∧ Nat.lcm 2 slot.a = 2 * slot.a := by
  intro ha
  obtain ⟨d, hd, rfl⟩ := Arithmetic.odd_a_type1 slot hv ha
  change 3 * d = 3 * d ∧ 2 * d < 3 * d ∧ 2 * d ≤ 3 * d ∧ Nat.lcm 2 d = 2 * d
  have hp : 0 < d := hd.pos
  exact ⟨rfl, by omega, by omega, hd.coprime_two_left.lcm_eq_mul⟩


theorem DivisorGraphRuleH.Arithmetic.a_dvd_two_iff (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) : slot.a ∣ 2 ↔ slot.a = 1 := by
  constructor
  · intro hdiv
    have hle := Nat.le_of_dvd (by decide : 0 < (2 : ℕ)) hdiv
    have hp := Arithmetic.a_pos slot hv
    have hn := Arithmetic.a_ne_two slot hv
    omega
  · intro heq
    rw [heq]
    exact one_dvd 2


theorem DivisorGraphRuleH.Arithmetic.aprime_dvd_two_iff (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) : slot.a' ∣ 2 ↔ slot.a' = 2 := by
  constructor
  · intro hdiv
    have hle := Nat.le_of_dvd (by decide : 0 < (2 : ℕ)) hdiv
    have hp := Arithmetic.two_le_aprime slot hv
    omega
  · intro heq
    rw [heq]


theorem DivisorGraphRuleH.Arithmetic.three_le_a_of_ne_one (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) : slot.a ≠ 1 → 3 ≤ slot.a := by
  intro hn
  have hp := Arithmetic.a_pos slot hv
  have htwo := Arithmetic.a_ne_two slot hv
  omega


theorem DivisorGraphRuleH.Arithmetic.odd_a_double_interior_bounds (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) : Odd slot.a → slot.a ≠ 1 →
    4 ≤ 2 * slot.a ∧ 2 * slot.a ≠ 1 ∧ 2 * slot.a ≠ 2 ∧
    Even (2 * slot.a) ∧ slot.a ∣ 2 * slot.a ∧ 2 * slot.a ≤ slot.size := by
  intro ho hn
  have h3 := Arithmetic.three_le_a_of_ne_one slot hv hn
  have hb := (Arithmetic.odd_a_moduli slot hv ho).2.2.1
  refine ⟨by omega, by omega, by omega, ?_, ?_, hb⟩
  · exact ⟨slot.a, by omega⟩
  · exact ⟨2, by omega⟩


def DivisorGraphRuleH.Arithmetic.results : Unit := ()
