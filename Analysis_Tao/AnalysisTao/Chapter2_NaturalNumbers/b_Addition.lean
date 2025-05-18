import Std.Classes
import AnalysisTao.Chapter2_NaturalNumbers.a_PeanoAxioms

namespace AnalysisTao.Chapter2_NaturalNumbers

open PeanoNat

--Definition 2.2.1 (Addition of natural numbers).
@[simp]
def add : PeanoNat → PeanoNat → PeanoNat
| zero,    m => m
| succ n,  m => PeanoNat.succ (add n m)

#check PeanoNat.induction

-- Lemma 2.2.2
theorem add_zero (n : PeanoNat) : add n zero = n := by
  induction n using PeanoNat.induction
  case hbase => rfl
  case hind n hn=>
    dsimp[add]
    rw[hn]

-- Lemma 2.2.3
theorem add_succ (n m : PeanoNat) : add n (succ m) = succ (add n m) := by
  induction n using PeanoNat.induction
  case hbase =>
    dsimp[add]
  case hind n hn=>
    dsimp[add]
    rw[hn]

-- Proposition 2.2.4 (Addition is commutative).
theorem add_comm (n m : PeanoNat) : add n m = add m n := by
  induction n using PeanoNat.induction
  case hbase =>
    dsimp[add]
    rw[add_zero]
  case hind n hn=>
    dsimp[add]
    rw[add_succ,hn]

-- Proposition 2.2.5 (Addition is associative).
theorem add_assoc (a b c : PeanoNat) : add (add a b) c = add a (add b c) := by
  induction c using PeanoNat.induction
  case hbase =>
    rw[add_zero,add_zero]
  case hind n hn=>
    rw[add_succ,hn,← add_succ,← add_succ]

-- Proposition 2.2.6 (Cancellation law).
theorem add_left_cancel {a b c : PeanoNat} (h : add a b = add a c) : b = c := by
  induction a using PeanoNat.induction
  case hbase =>
    dsimp[add] at h
    apply h
  case hind n hn=>
    dsimp at h
    have h': add n b = add n c := succ_inj h
    apply (hn h')

theorem add_right_cancel {a b c : PeanoNat} (h : add b a = add c a) : b = c := by
  have h': add a b = add a c:= by
    rw[add_comm a b,add_comm a c]
    apply h
  apply add_left_cancel h'

-- Definition 2.2.7 (Positive natural numbers).
def positive (n : PeanoNat) : Prop :=
  n ≠ zero

-- Proposition 2.2.8
theorem add_pos_of_pos {a b : PeanoNat} (ha : positive a) : positive (add a b) := by
  induction b using PeanoNat.induction
  case hbase =>
    dsimp [add, positive]
    rw[add_zero]
    apply ha
  case hind b hn =>
    dsimp [add]
    rw[add_succ]
    intro h
    simp at h

-- Corollary 2.2.9
theorem add_eq_zero_iff {a b : PeanoNat} (h : add a b = zero) : a = zero ∧ b = zero := by
  by_cases ha : a = zero
  · rw [ha] at h
    dsimp [add] at h
    exact ⟨ha, h⟩
  · have ha_pos : positive a := ha
    have hab_ne_zero : add a b ≠ zero := add_pos_of_pos ha_pos
    contradiction

-- Lemma 2.2.10
theorem ext_one_pred {a : PeanoNat} (ha : positive a) : ∃ b, succ b = a := by
  induction a using PeanoNat.induction
  case hbase =>
    dsimp [positive] at ha
    contradiction
  case hind a hn =>
    apply Exists.intro a
    rfl

-- Definition 2.2.11 (Ordering of the natural numbers).
/-- `n ≥ m` means `n = m + a` for some `a`. -/
def ge (n m : PeanoNat) : Prop :=
  ∃ a, add m a = n
/-- `n > m` means `n ≥ m` and `n ≠ m`. -/
def gt (n m : PeanoNat) : Prop :=
  ge n m ∧ n ≠ m

-- Enable notations for ordering
notation:50 n " ≥ " m => ge n m
notation:50 n " ≤ " m => ge m n
notation:50 n " > " m => gt n m
notation:50 n " < " m => gt m n

--lemma
theorem Pnat_ge_zero (n : PeanoNat) : n ≥ zero := by
  dsimp[ge]
  apply Exists.intro n
  rfl

-- Proposition 2.2.12 (Basic properties of order).

-- (Order is reflexive)
theorem ge_refl (n : PeanoNat) : n ≥ n := by
  apply Exists.intro zero
  apply add_zero

-- (Order is transitive)
theorem ge_trans {a b c : PeanoNat} (hab : a ≥ b) (hbc : b ≥ c) : a ≥ c := by
  rcases hab with ⟨d, hd⟩
  rcases hbc with ⟨e, he⟩
  apply Exists.intro (add e d)
  calc
    add c (add e d) = add (add c e) d := by rw [add_assoc]
    _ = add b d := by rw [he]
    _ = a := by rw [← hd]

--lemma
theorem add_eq_zero {a b : PeanoNat}(hab: add a b =zero): a=zero ∧ b=zero:= by
  induction a using PeanoNat.induction
  case hbase =>
    constructor
    · rfl
    · dsimp at hab
      apply hab
  case hind a hn =>
    constructor
    · dsimp at hab
      have hab': (add a b).succ ≠ zero := succ_ne_zero
      contradiction
    · dsimp at hab
      have hab': (add a b).succ ≠ zero := succ_ne_zero
      contradiction

-- (Order is anti-symmetric)
theorem ge_antisymm {a b : PeanoNat} (hab : a ≥ b) (hba : b ≥ a) : a = b := by
  rcases hab with ⟨d, hd⟩
  rcases hba with ⟨e, he⟩
  rw[← hd,add_assoc] at he
  have he': add b (add d e) = add b zero := by
    rw[add_zero]
    apply he
  have hde: add d e = zero := add_left_cancel he'
  have zero_de: d = zero ∧ e = zero := add_eq_zero hde
  rw[zero_de.left,add_zero] at hd
  apply hd.symm

--lemma
theorem succ_ge_succ {a b: PeanoNat} : (a ≥ b) ↔ a.succ ≥ b.succ := by
  constructor
  · intro hba
    rcases hba with ⟨c, h⟩
    apply Exists.intro c
    dsimp
    rw[h]
  · intro hba_succ
    rcases hba_succ with ⟨c, h⟩
    apply Exists.intro c
    dsimp at h
    apply succ_inj h

-- (Addition preserves order)
theorem add_ge_add {a b c : PeanoNat} : (a ≥ b) ↔ add a c ≥ add b c := by
  constructor
  · intro hba
    induction c using PeanoNat.induction
    case hbase =>
      rw[add_zero,add_zero]
      apply hba
    case hind d hn =>
      rw[add_succ,add_succ]
      apply succ_ge_succ.mp
      apply hn
  · intro hba
    induction c using PeanoNat.induction
    case hbase =>
      rw[add_zero,add_zero] at hba
      apply hba
    case hind d hn =>
      rw[add_succ,add_succ] at hba
      apply hn (succ_ge_succ.mpr hba)

--lemma
theorem ne_zero_gt_zero {a : PeanoNat} : a ≠ zero → a > zero := by
  intro haz
  dsimp[gt]
  constructor
  · apply Pnat_ge_zero
  · apply haz

--lemma
theorem succ_gt {a: PeanoNat} : a.succ > a := by
  dsimp[gt]
  constructor
  · apply Exists.intro 1
    have h₁ : PeanoNat.succ zero = 1 := rfl
    rw[← h₁,add_succ,add_zero]
  · apply succ_ne

-- a < b if and only if succ a ≤ b
theorem lt_iff_succ_ge (a b : PeanoNat) : (a < b) ↔ succ a ≤ b := by
  dsimp [gt, ge]
  constructor
  · intro h
    rcases h with ⟨⟨ c, hbc⟩, hne⟩
    have cne_zero: c ≠ zero := by
      intro ceq_zero
      rw[ceq_zero,add_zero] at hbc
      exact hne (Eq.symm hbc)
    have c_pre: ∃ d, succ d = c := ne_succ cne_zero
    rcases c_pre with ⟨d,hd⟩
    apply Exists.intro d
    rw[← hd,add_succ] at hbc
    exact hbc
  · intro h
    rcases h with ⟨d, hd⟩
    constructor
    · apply Exists.intro (d.succ)
      rw [add_succ,hd]
    · intro eqab
      have hbd: add b d.succ = add b zero := by rw [add_succ,eqab,hd,add_zero,eqab]
      have hd': d.succ = zero := add_left_cancel hbd
      apply succ_ne_zero hd'

-- a < b if and only if b = a + d for some positive d
theorem lt_iff_add_pos {a b : PeanoNat} : (a < b) ↔ ∃ d, positive d ∧ add a d = b := by
  constructor
  · intro hab
    dsimp [gt] at hab
    rcases hab with ⟨ ge_ab, ne_ab⟩
    dsimp [ge] at ge_ab
    rcases ge_ab with ⟨ c, hab'⟩
    induction c using PeanoNat.induction
    case hbase =>
      rw[add_zero] at hab'
      rw[hab'] at ne_ab
      contradiction
    case hind c hn =>
      apply Exists.intro c.succ
      constructor
      · apply succ_ne_zero
      · apply hab'
  · intro habd
    rcases habd with ⟨ d, pos_d, hab⟩
    dsimp [gt]
    constructor
    · dsimp [ge]
      apply Exists.intro d
      apply hab
    · intro eq_ab
      have hab': add a zero = b := by rw[eq_ab,add_zero]
      rw[← hab'] at hab
      have hd: d = zero := add_left_cancel hab
      contradiction

--lemma
theorem dichotomy (a b : PeanoNat) : (a ≤ b) ∨ (a ≥ b) := by
  sorry

-- Proposition 2.2.13 (Trichotomy of order for natural numbers).
theorem trichotomy (a b : PeanoNat) : (a < b) ∨ (a = b) ∨ (a > b) := by
  by_cases h₁ : a = b
  · exact Or.inr (Or.inl h₁)
  · by_cases h₂ : a ≤ b
    · have hab: a < b := by
        dsimp[gt,ge]
        constructor
        · apply h₂
        · intro eq_ab
          rw[eq_ab] at h₁
          contradiction
      apply Or.inl hab
    · have hab: a ≥ b := by
        apply Or.elim (dichotomy a b)
        · intro h_le; exact False.elim (h₂ h_le)
        · intro h_ge; exact h_ge
      have hab': b < a := by
        dsimp[gt,ge]
        constructor
        · apply hab
        · intro eq_ab
          rw[eq_ab] at h₁
          contradiction
      apply Or.inr (Or.inr hab')

-- Proposition 2.2.14 (Strong principle of induction).
theorem strong_induction{m m₀ : PeanoNat} {P  : PeanoNat → Prop}
  (hbase : P m₀) (hstep : ∀ m, (∀ k, (k < m) → P k) → P m)
  : ∀ m, (m ≥ m₀) → P m := by
  sorry

end AnalysisTao.Chapter2_NaturalNumbers
