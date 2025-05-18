namespace AnalysisTao.Chapter2_NaturalNumbers

-- Axiom 2.1: Zero is a natural number
-- Axiom 2.2: If n is a natural number, then n++ is also a naturalnumber.
inductive PeanoNat : Type where
  | zero
  | succ (n : PeanoNat)

-- Axiom 2.3: Zero is not the successor of any number
axiom PeanoNat.succ_ne_zero : ∀ {n : PeanoNat}, PeanoNat.succ n ≠ PeanoNat.zero

-- Axiom 2.4: Different natural numbers must have different successors
axiom PeanoNat.succ_inj : ∀ {n m : PeanoNat}, PeanoNat.succ n = PeanoNat.succ m → n = m

-- Axiom 2.4′: Equivalent to Axiom 2.4 (contrapositive form)
axiom PeanoNat.succ_inj' : ∀ {n m : PeanoNat}, n ≠ m → PeanoNat.succ n ≠ PeanoNat.succ m

-- Axiom 2.5: Induction principle
axiom PeanoNat.induction {P : PeanoNat → Prop}
  (hbase : P PeanoNat.zero)(hind  : ∀ {n : PeanoNat}, P n → P (PeanoNat.succ n))
  : ∀ n, P n

-- Example theorem
theorem succ_ne {a: PeanoNat} : a.succ ≠ a := by
  induction a using PeanoNat.induction
  case hbase =>
    apply PeanoNat.succ_ne_zero
  case hind d hn =>
    apply PeanoNat.succ_inj'
    exact hn

-- Numeric support for PeanoNat
noncomputable instance : OfNat PeanoNat 0 := ⟨PeanoNat.zero⟩
noncomputable instance : OfNat PeanoNat 1 := ⟨PeanoNat.succ 0⟩
noncomputable instance : OfNat PeanoNat 2 := ⟨PeanoNat.succ 1⟩
noncomputable instance : OfNat PeanoNat 3 := ⟨PeanoNat.succ 2⟩
noncomputable instance : OfNat PeanoNat 4 := ⟨PeanoNat.succ 3⟩
noncomputable instance : OfNat PeanoNat 5 := ⟨PeanoNat.succ 4⟩
noncomputable instance : OfNat PeanoNat 6 := ⟨PeanoNat.succ 5⟩

-- Proposition 2.1.8
theorem six_ne_two : (6 : PeanoNat) ≠ (2 : PeanoNat) := by
  have h₆ : PeanoNat.succ 5 = 6 := rfl
  have h₂ : PeanoNat.succ 1 = 2 := rfl
  intro eq_6_2
  have h_succ : PeanoNat.succ 5 = PeanoNat.succ 1 := by
    rw[h₆,h₂]
    apply eq_6_2
  have eq_5_1 : (5 : PeanoNat) = 1 := PeanoNat.succ_inj h_succ
  have h₅ : PeanoNat.succ 4 = 5 := rfl
  have h₁ : PeanoNat.succ 0 = 1 := rfl
  have h_succ4_zero_succ : PeanoNat.succ 4 = PeanoNat.succ 0 := by
    rw[h₅,h₁]
    apply eq_5_1
  have eq_4_0 : (4 : PeanoNat) = 0 := PeanoNat.succ_inj h_succ4_zero_succ
  have h₄ : 4 = PeanoNat.succ 3 := rfl
  rw[h₄] at eq_4_0
  exact (PeanoNat.succ_ne_zero eq_4_0)

-- Example theorem
theorem ne_succ {a: PeanoNat} (hab : a ≠ 0): ∃ c, PeanoNat.succ c = a := by
  induction a using PeanoNat.induction
  case hbase =>
    contradiction
  case hind b hn =>
    apply Exists.intro b
    rfl

end AnalysisTao.Chapter2_NaturalNumbers
