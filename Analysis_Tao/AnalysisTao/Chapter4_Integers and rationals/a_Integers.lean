import Std.Classes
import Std.Tactic

import AnalysisTao.Chapter2_NaturalNumbers

namespace Chapter3

open Chapter2
open PeanoNat
open Classical

structure IntPair where
  fst : PeanoNat
  snd : PeanoNat

def int_eq (p1 p2 : IntPair) : Prop :=
  add p1.fst p2.snd = add p2.fst p1.snd

theorem Int_eq_refl (p : IntPair) : int_eq p p := by
  dsimp [int_eq]

theorem Int_int_eq_symm {p1 p2 : IntPair} (h : int_eq p1 p2) : int_eq p2 p1 := by
  dsimp [int_eq]
  exact h.symm

theorem int_eq_trans {p1 p2 p3 : IntPair} (h1 : int_eq p1 p2) (h2 : int_eq p2 p3) : int_eq p1 p3 := by
  dsimp [int_eq]
  have h : add (add p1.fst p3.snd) p2.snd = add (add p3.fst p1.snd) p2.snd := by
    calc
      add (add p1.fst p3.snd) p2.snd
        = add p1.fst (add p3.snd p2.snd)      := by rw [add_assoc]
      _ = add p1.fst (add p2.snd p3.snd)      := by rw [add_comm p3.snd p2.snd]
      _ = add (add p1.fst p2.snd) p3.snd      := by rw [add_assoc]
      _ = add (add p2.fst p1.snd) p3.snd      := by rw [h1]
      _ = add p2.fst (add p1.snd p3.snd)      := by rw [add_assoc]
      _ = add p2.fst (add p3.snd p1.snd)      := by rw [add_comm p1.snd p3.snd]
      _ = add (add p2.fst p3.snd) p1.snd      := by rw [add_assoc]
      _ = add (add p3.fst p2.snd) p1.snd      := by rw [h2]
      _ = add p3.fst (add p2.snd p1.snd)      := by rw [add_assoc]
      _ = add p3.fst (add p1.snd p2.snd)      := by rw [add_comm p2.snd p1.snd]
      _ = add (add p3.fst p1.snd) p2.snd      := by rw [add_assoc]
  apply add_right_cancel h

instance int_setoid : Setoid IntPair where
  r := int_eq
  iseqv := { refl := @Int_eq_refl, symm := @Int_int_eq_symm, trans := @int_eq_trans }

def Integer : Type := Quotient int_setoid

def mkInt (a b : PeanoNat) : Integer := Quotient.mk int_setoid { fst := a, snd := b }

notation:65 a " -- " b => mkInt a b

def add_Int (p1 p2 : IntPair) : IntPair :=
  { fst := add p1.fst p2.fst, snd := add p1.snd p2.snd }

def mul_Int (p1 p2 : IntPair) : IntPair :=
  { fst := add (mul p1.fst p2.fst) (mul p1.snd p2.snd),
    snd := add (mul p1.fst p2.snd) (mul p1.snd p2.fst) }



end Chapter3
