import PowerCalc.Examples.Groups.Basic
import Aesop

open G

@[aesop unsafe 50%]
axiom assocMul: forall (a b c: G), a * (b * c) = (a * b) * c
@[aesop unsafe 50%]
axiom invLeft: forall (a: G), (inv a) * a = one
@[aesop unsafe 50%]
axiom oneMul: forall (a: G), one * a = a
@[aesop unsafe 50%]
axiom mulOne: forall (a: G), a * one = a
@[aesop unsafe 50%]
axiom invRight: forall (a: G), a * (inv a) = one



theorem inv_inv
  (x: G)
  : (inv (inv x) = x) := by aesop

theorem inv_mul_cancel_left
  (assocMul: forall (a b c: G), a * (b * c) = (a * b) * c)
  (invLeft: forall (a: G), (inv a) * a = one)
  (oneMul: forall (a: G), one * a = a)
  (mulOne: forall (a: G), a * one = a)
  (invRight: forall (a: G), a * (inv a) = one)
  (x: G)
  (x y : G)
  : ((inv x) * (x * y)) = y := by aesop


theorem mul_inv_cancel_left
  (assocMul: forall (a b c: G), a * (b * c) = (a * b) * c)
  (invLeft: forall (a: G), (inv a) * a = one)
  (oneMul: forall (a: G), one * a = a)
  (mulOne: forall (a: G), a * one = a)
  (invRight: forall (a: G), a * (inv a) = one)
  (x y : G)
  : x * ((inv x) * y) = y := by aesop

theorem inv_mul
  (assocMul: forall (a b c: G), a * (b * c) = (a * b) * c)
  (invLeft: forall (a: G), (inv a) * a = one)
  (oneMul: forall (a: G), one * a = a)
  (mulOne: forall (a: G), a * one = a)
  (invRight: forall (a: G), a * (inv a) = one)
  (x y : G)
  : (inv (x * y)) = ((inv y) * (inv x)) := by aesop
  
theorem one_inv
  (assocMul: forall (a b c: G), a * (b * c) = (a * b) * c)
  (invLeft: forall (a: G), (inv a) * a = one)
  (oneMul: forall (a: G), one * a = a)
  (mulOne: forall (a: G), a * one = a)
  (invRight: forall (a: G), a * (inv a) = one)
  : (inv one) = one := by aesop

