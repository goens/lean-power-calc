import PowerCalc.Examples.PolynomialsPerformance.Basic

--set_option trace.EggTactic.egg true in
-- open R in
-- theorem test
--   (comm_add : forall a b : R,  a + b = b + a)
--   (comm_mul:  forall a b : R, a * b = b * a)
--   (add_assoc: forall a b c : R, a + (b + c) = (a + b) + c)
--   (mul_assoc: forall a b c : R, a * (b * c) = (a * b) * c)
--   (sub_canon: forall a b : R, (a - b)  = a + ((R.neg one) * b))
--   (neg_add : forall a : R , a + (R.neg a) = zero)
--   (div_canon : forall a b : R, (a / b) = a * (R.inv b))
--   (zero_add: forall a : R, a + zero = a )
--   (zero_mul: forall a : R, a * zero = zero)
--   (one_mul: forall a : R,  a * one = a)
--   (distribute: forall a b c : R, a * (b + c)  = (a * b) + (a * c))
--   (factorial_case : forall n : R, (n)! =  n * (n - one)!)
--   (factorial_one : forall n : R, (one)! = one )
--   (factorial_zero : forall n : R, (zero)! = one)
--   (neg_neg : forall a : R, (R.neg (R.neg a)) = a)
--   (neg_one_mul : forall a : R, (R.neg one) * a = R.neg a)
--   (binomial_helper : forall n r : R, (R.choose (n + one) r) = ((R.choose n (r - one)) + (R.choose n r)))
--   (n : R)
--   (inductive_hypothesis : forall r : R, (R.choose n r) = (n)! / ((r)! * (n - r)!)) 
--   (r : R) :
--   (n - (r - one) = (n - r + one)) := by eggcalcB -- rw [sub_canon, sub_canon, distribute (neg one), one_mul, neg_one_mul (neg one), neg_neg, neg_one_mul, ← sub_canon]
-- 

open R in
theorem Rotman_1_15
  (comm_add : forall a b : R,  a + b = b + a)
  (comm_mul:  forall a b : R, a * b = b * a)
  (add_assoc: forall a b c : R, a + (b + c) = (a + b) + c)
  (mul_assoc: forall a b c : R, a * (b * c) = (a * b) * c)
  (sub_canon: forall a b : R, (a - b)  = a + ((R.neg one) * b))
  (neg_add : forall a : R , a + (R.neg a) = zero)
  (neg_neg : forall a : R, (R.neg (R.neg a)) = a)
  (neg_one_mul : forall a : R, (R.neg one) * a = R.neg a)
  (sub_add : forall a b c : R, a - (b - c) = a - b + c)
  (div_canon : forall a b : R, (a / b) = a * (R.inv b))
  (zero_add: forall a : R, a + zero = a )
  (zero_mul: forall a : R, a * zero = zero)
  --(mul_div_comm : forall a b c : R, (a * b) / c = (a / c) * b)
  --(div_mul_comm : forall a b c : R, (a / b) * c = (a * c) / b)
  (mul_div_assoc : forall a b c : R, a * (b / c) = (a * b) / c)
  --(div_mul_assoc : forall a b c : R, (a / b) * c = a * c / b)
  --(mul_inv : forall a : R, a * (R.inv a) = one) -- this is wrong... but we can't add it with the condition here
  (add_fractions : forall a b c d : R, (a / b) + (c / d) = (a * d + b * c) / (b * d))
  (mul_fractions : forall a b c d : R , (a / b) * (c / d) = (a * c) / (b * d))
  (one_mul: forall a : R,  a * one = a)
  (distribute: forall a b c : R, a * (b + c)  = (a * b) + (a * c))
  (factor_div : forall a b c d e f: R , (a / b) * (c/d + e/f) = (a * c) / (b * d) + (a * e) / (b * f))
  (factorial_case : forall n : R, (n)! =  n * (n - one)!)
  (factorial_case2 : forall n : R, (n + one)! = (n + one) * (n!))
  (factorial_one : forall n : R, (one)! = one )
  (factorial_zero : forall n : R, (zero)! = one)
  (binomial_helper : forall n r : R, (R.choose (n + one) r) = ((R.choose n (r - one)) + (R.choose n r)))
  (n : R)
  (inductive_hypothesis : forall r : R, (R.choose n r) = (n)! / ((r)! * (n - r)!))
  : forall r : R, (R.choose (n + one) r) =  (n + one)! / (r! * (n + one - r)!)
   := by
     intro r
     calc (R.choose (n + one) r) = (R.choose n (r - one)) + (R.choose n r) := by rw [binomial_helper] 
     _ = n ! / ((r - one)! * ((n - r) + one)!) + n ! / (r ! * (n - r)!) := by rw [inductive_hypothesis (r - one), inductive_hypothesis, sub_add]
     _ = (n)! / ((r - one)! * (n - r)!) * (one / (n - r + one) + one/r) := by rw [factorial_case (n - r + one), sub_canon (n - r + one) one, ← add_assoc _ _ (neg one * one), one_mul, neg_add _, zero_add, comm_mul (n - r + one), mul_assoc, factorial_case r, comm_mul r _, ← mul_assoc _ r _, comm_mul r _, mul_assoc, ← one_mul ((n)!), ← factor_div, one_mul]
     _ = ((n)! / ((r -one)! * (n - r)!)) * ((r + (n - r + one)) / (r * (n - r + one))) := by rw [add_fractions, comm_mul one, one_mul, one_mul, comm_mul _ r , mul_div_assoc] --by eggcalcB
     _ = (n + one)! / r! * (n + one - r)! := by rw [mul_fractions, sub_canon, add_assoc r _ one, comm_add n _, add_assoc, neg_one_mul, neg_add, comm_add zero _, zero_add, comm_mul, factorial_case2]


/-
= n! / (r -one)! (n - r + one)! + n!/(r! * (n - one)!)
= n! / (r -one)! (n - r)! * ((n - r + one) + one/r)
= n! / (r -one)! (n - r)! * (r + n - r + one / r * (n - r + one))
= n! / (r -one)! (n - r)! * (n + one / r * (n - r + one))
= (n + one)! / r! * (n + one - r)!
-/