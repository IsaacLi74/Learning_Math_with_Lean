prelude
import Init
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

--a small lemma before "Order is anti-symmetric"
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

-- (Addition preserves order)
theorem add_le_add {a b c : PeanoNat} : (a ≥ b) ↔ add a c ≥ add b c := by
  constructor
  · sorry
  · sorry

-- a < b if and only if succ a ≥ b
theorem lt_iff_succ_ge (a b : PeanoNat) : (a < b) ↔ succ a ≥ b := by
  constructor
  · sorry
  · sorry

-- a < b if and only if b = a + d for some positive d
theorem lt_iff_add_pos {a b : PeanoNat} : (a < b) ↔ ∃ d, positive d ∧ add a d = b := by
  constructor
  · sorry
  · sorry

end AnalysisTao.Chapter2_NaturalNumbers
