import Std.Classes
import Std.Tactic

import AnalysisTao.Chapter2_NaturalNumbers.a_PeanoAxioms
import AnalysisTao.Chapter2_NaturalNumbers.b_Addition

namespace Chapter2

open PeanoNat
open Classical

/-- Definition 2.3.1 (Multiplication of natural numbers). -/
@[simp]
def mul : PeanoNat → PeanoNat → PeanoNat
| zero,    _ => zero
| succ n,  m => add (mul n m) m

theorem mul_zero (n : PeanoNat) : mul n zero = zero := by
  induction n using PeanoNat.induction
  case hbase => rfl
  case hind n ih => dsimp [mul]; rw [ih, add_zero]

theorem mul_succ (n m : PeanoNat) : mul n (succ m) = add (mul n m) n := by
  induction n using PeanoNat.induction
  case hbase => rfl
  case hind n ih =>
    dsimp [mul]
    rw [ih,add_succ,add_succ,add_assoc,add_assoc,add_comm m n]

/-- Lemma 2.3.2 (Multiplication is commutative). -/
theorem mul_comm (n m : PeanoNat) : mul n m = mul m n := by
  induction n using PeanoNat.induction
  case hbase =>
    simp [mul]
    rw[mul_zero]
  case hind n ih =>
    dsimp [mul]
    rw [ih, (mul_succ m n).symm]

/-- Lemma 2.3.3 (Natural numbers have no zero divisors). -/
theorem mul_eq_zero_iff {n m : PeanoNat} : mul n m = zero ↔ n = zero ∨ m = zero := by
  induction n using PeanoNat.induction
  case hbase => simp [mul]
  case hind n ih =>
    constructor
    · simp[mul]
      intro hnm_zero
      have hnm := add_eq_zero_iff hnm_zero
      apply hnm.2
    · simp[mul]
      intro hm
      have hmn: mul n m = zero := ih.mpr (Or.inr hm)
      rw[hmn,hm,add_zero]

/-- Proposition 2.3.4 (Distributive law): a * (b + c) = a*b + a*c. -/
theorem mul_add (a b c : PeanoNat) : mul a (add b c) = add (mul a b) (mul a c) := by
  induction a using PeanoNat.induction
  case hbase => rfl
  case hind a ih =>
    dsimp [mul]
    rw[ih,← add_assoc,add_assoc (mul a b),add_comm (mul a c),← add_assoc,add_assoc]

/-- Distributivity on the right: (b + c) • a = b • a + c • a. -/
theorem add_mul (b c a : PeanoNat) : mul (add b c) a = add (mul b a) (mul c a) := by
  calc
    mul (add b c) a = mul a (add b c) := by rw [mul_comm]
    _ = add (mul a b) (mul a c)      := mul_add a b c
    _ = add (mul b a) (mul c a)      := by rw [mul_comm, mul_comm c a]

/-- Proposition 2.3.5 (Multiplication is associative). -/
theorem mul_assoc (a b c : PeanoNat) : mul (mul a b) c = mul a (mul b c) := by
  induction a using PeanoNat.induction
  case hbase => rfl
  case hind a ih =>
    dsimp [mul]
    rw [add_mul, ih]

/-- Proposition 2.3.6 (Multiplication preserves order): if a < b and c ≠ 0 then c • a < c • b. -/
theorem mul_lt_mul_of_positive {a b c : PeanoNat} (h : a < b) (hc : c ≠ zero) : (mul c a) < mul c b := by
  have hab := lt_iff_add_pos.mp h
  rcases hab with ⟨d, hd⟩
  simp[gt]
  constructor
  · simp[ge]
    apply Exists.intro (mul c d)
    rw[mul_comm c a,mul_comm c d,← add_mul,hd.2,mul_comm]
  · rw[← hd.2,mul_add]
    intro contra
    have contra': add (mul c a) (mul c d) = add (mul c a) zero := by
      rw[add_zero]
      apply contra
    have hcd:= mul_eq_zero_iff.mp (add_left_cancel contra')
    cases hcd with
    | inl hczero  => exact hc hczero
    | inr hdzero  => exact hd.1  hdzero

/-- Corollary 2.3.7 (Cancellation law): if a • c = b • c and c ≠ 0 then a = b. -/
theorem mul_left_cancel {a b c : PeanoNat} (h : mul a c = mul b c) (hc : c ≠ zero) : a = b := by
  cases trichotomy a b with
  | inl hab_lt =>
    have hlt := mul_lt_mul_of_positive hab_lt hc
    have hne := hlt.2
    have heq := by rw [mul_comm a c, mul_comm b c] at h; exact h.symm
    contradiction
  | inr eq_or =>
    cases eq_or with
    | inl heq => exact heq
    | inr hgt =>
      have hlt := mul_lt_mul_of_positive hgt hc
      have hne := hlt.2
      have heq := by rw [mul_comm a c, mul_comm b c] at h; exact h
      contradiction

/-- Proposition 2.3.9 (Euclidean algorithm).
Let `n` be a natural number, and let `q` be a positive number.
Then there exist natural numbers `m` and `r` such that `r < q` and `n = m • q + r`. -/
theorem euclidean_div_mod (n q : PeanoNat) (hq : q ≠ zero) :
  ∃ m r : PeanoNat, (r < q) ∧ n = add (mul m q) r := by
    induction n using PeanoNat.induction
    case hbase =>
      apply Exists.intro zero
      apply Exists.intro zero
      simp
      dsimp[gt]
      exact ⟨Pnat_ge_zero q,hq⟩
    case hind a ih =>
    rcases ih with ⟨m, r, hr_lt, ha⟩
    by_cases h : succ r = q
    · apply Exists.intro m.succ
      apply Exists.intro zero
      constructor
      · apply ne_zero_gt_zero hq
      · rw [ha,← add_succ,h]
        simp
        rw[add_zero]
    · apply Exists.intro m
      apply Exists.intro r.succ
      constructor
      · rcases lt_iff_add_pos.mp hr_lt with ⟨d, hd_pos, hd_eq⟩
        rcases ext_one_pred hd_pos with ⟨e, rfl⟩
        dsimp[gt,ge]
        constructor
        · apply Exists.intro e
          rw[← add_succ,hd_eq]
        · intro hqr
          rw[hqr] at h
          contradiction
      · rw [ha, ← add_succ]

/-- Definition 2.3.11 (Exponentiation for natural numbers). -/
@[simp]
def pow : PeanoNat → PeanoNat → PeanoNat
| _    , zero    => succ zero
| m    , succ n => mul (pow m n) m

-- exercise: pick some theorems by your own and prove them!

end Chapter2
