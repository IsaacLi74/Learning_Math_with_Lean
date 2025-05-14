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

-- Lemma 2.2.2
theorem add_zero (n : PeanoNat) : add n 0 = n := by
  induction n using PeanoNat.induction
  case hbase => rfl
  case hind n hn=>
    dsimp
    rw[hn]

-- Lemma 2.2.3
theorem add_succ (n m : PeanoNat) : add n (succ m) = succ (add n m) := by
  sorry

-- Proposition 2.2.4 (Addition is commutative).
theorem add_comm (n m : PeanoNat) : add n m = add m n := by
  sorry

-- Proposition 2.2.5 (Addition is associative).
theorem add_assoc (a b c : PeanoNat) : add (add a b) c = add a (add b c) := by
  sorry

-- Proposition 2.2.6 (Cancellation law).
theorem add_left_cancel {a b c : PeanoNat} (h : add a b = add a c) : b = c := by
  sorry

end AnalysisTao.Chapter2_NaturalNumbers
