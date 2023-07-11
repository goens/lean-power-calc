import PowerCalc.Examples.Groups.Basic

open G

theorem inv_inv
  (assocMul: forall (a b c: G), a * (b * c) = (a * b) * c)
  (invLeft: forall (a: G), (inv a) * a = one)
  (oneMul: forall (a: G), one * a = a)
  (mulOne: forall (a: G), a * one = a)
  (invRight: forall (a: G), a * (inv a) = one)
  (x: G)
  : (inv (inv x) = x) := by simp[assocMul, invLeft, oneMul, mulOne, invRight]

theorem inv_mul_cancel_left
  (assocMul: forall (a b c: G), a * (b * c) = (a * b) * c)
  (invLeft: forall (a: G), (inv a) * a = one)
  (oneMul: forall (a: G), one * a = a)
  (mulOne: forall (a: G), a * one = a)
  (invRight: forall (a: G), a * (inv a) = one)
  (x: G)
  (x y : G)
  : ((inv x) * (x * y)) = y := by simp[assocMul, invLeft, oneMul, mulOne, invRight]


theorem mul_inv_cancel_left
  (assocMul: forall (a b c: G), a * (b * c) = (a * b) * c)
  (invLeft: forall (a: G), (inv a) * a = one)
  (oneMul: forall (a: G), one * a = a)
  (mulOne: forall (a: G), a * one = a)
  (invRight: forall (a: G), a * (inv a) = one)
  (x y : G)
  : x * ((inv x) * y) = y := by simp[assocMul, invLeft, oneMul, mulOne, invRight]

theorem inv_mul
  (assocMul: forall (a b c: G), a * (b * c) = (a * b) * c)
  (invLeft: forall (a: G), (inv a) * a = one)
  (oneMul: forall (a: G), one * a = a)
  (mulOne: forall (a: G), a * one = a)
  (invRight: forall (a: G), a * (inv a) = one)
  (x y : G)
  : (inv (x * y)) = ((inv y) * (inv x)) := by simp[assocMul, invLeft, oneMul, mulOne, invRight]
  
theorem one_inv
  (assocMul: forall (a b c: G), a * (b * c) = (a * b) * c)
  (invLeft: forall (a: G), (inv a) * a = one)
  (oneMul: forall (a: G), one * a = a)
  (mulOne: forall (a: G), a * one = a)
  (invRight: forall (a: G), a * (inv a) = one)
  : (inv one) = one := by simp[assocMul, invLeft, oneMul, mulOne, invRight]

