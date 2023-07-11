import PowerCalc.Examples.Groups.Basic

open G

theorem inv_inv
  (assocMul: forall (a b c: G), a * (b * c) = (a * b) * c)
  (invLeft: forall (a: G), (inv a) * a = one)
  (oneMul: forall (a: G), one * a = a)
  (mulOne: forall (a: G), a * one = a)
  (invRight: forall (a: G), a * (inv a) = one)
  (x: G)
  : (inv (inv x) = x) := by calc
  inv (inv x) = inv (inv x) * one := by ges
             _ = (inv (inv x))*((inv x) * x) := by ges
             _ = x := by ges

theorem inv_mul_cancel_left
  (assocMul: forall (a b c: G), a * (b * c) = (a * b) * c)
  (invLeft: forall (a: G), (inv a) * a = one)
  (oneMul: forall (a: G), one * a = a)
  (mulOne: forall (a: G), a * one = a)
  (invRight: forall (a: G), a * (inv a) = one)
  (x: G)
  (x y : G)
  : ((inv x) * (x * y)) = y := by ges


theorem mul_inv_cancel_left
  (assocMul: forall (a b c: G), a * (b * c) = (a * b) * c)
  (invLeft: forall (a: G), (inv a) * a = one)
  (oneMul: forall (a: G), one * a = a)
  (mulOne: forall (a: G), a * one = a)
  (invRight: forall (a: G), a * (inv a) = one)
  (x y : G)
  : x * ((inv x) * y) = y := by ges

theorem inv_mul
  (assocMul: forall (a b c: G), a * (b * c) = (a * b) * c)
  (invLeft: forall (a: G), (inv a) * a = one)
  (oneMul: forall (a: G), one * a = a)
  (mulOne: forall (a: G), a * one = a)
  (invRight: forall (a: G), a * (inv a) = one)
  (x y : G)
  : (inv (x * y)) = ((inv y) * (inv x)) := by calc
   (inv (x * y)) = (inv (x * y)) * one := by ges
    _ = (inv (x * y)) * one := by ges
    _ = (inv (x * y)) * (y * (inv y)) := by ges
    _ = (inv y) * (inv x) := sorry
  
theorem one_inv
  (assocMul: forall (a b c: G), a * (b * c) = (a * b) * c)
  (invLeft: forall (a: G), (inv a) * a = one)
  (oneMul: forall (a: G), one * a = a)
  (mulOne: forall (a: G), a * one = a)
  (invRight: forall (a: G), a * (inv a) = one)
  : (inv one) = one := by ges

