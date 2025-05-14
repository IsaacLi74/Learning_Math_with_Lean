prelude
import Init
import AnalysisTao.Chapter2_NaturalNumbers.a_PeanoAxioms

namespace AnalysisTao.Chapter2_NaturalNumbers

open PeanoNat

--Definition 2.2.1 (Addition of natural numbers).
def add : PeanoNat → PeanoNat → PeanoNat
| zero,    m => m
| succ n,  m => PeanoNat.succ (add n m)

--Lemma 2.2.2: For any natural number n, n + 0 = n.

--Lemma 2.2.3: For any natural numbers n and m, n+(m++) = (n + m)++.

--Proposition 2.2.4 (Addition is commutative).

--Proposition 2.2.5 (Addition is associative).

--Proposition 2.2.6 (Cancellation law).

end AnalysisTao.Chapter2_NaturalNumbers
