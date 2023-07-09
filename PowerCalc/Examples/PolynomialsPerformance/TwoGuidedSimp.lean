import PowerCalc.Examples.PolynomialsPerformance.Basic


set_option maxHeartbeats 10000000
theorem freshmans_dream
  (two : R )
  (comm_add : forall a b : R,  a + b = b + a)
  (comm_mul:  forall a b : R, a * b = b * a)
  (add_assoc: forall a b c : R, a + (b + c) = (a + b) + c)
  (mul_assoc: forall a b c : R, a * (b * c) = (a * b) * c)
  (sub_canon: forall a b : R, (a - b)  = a + (R.neg b))
  (neg_add : forall a : R , a + (R.neg a) = zero)
  (div_canon : forall a b : R, (a / b) = a * (R.inv b))
  (zero_add: forall a : R, a + zero = a )
  (zero_mul: forall a : R, a * zero = zero)
  (one_mul: forall a : R,  a * one = a)
  (distribute: forall a b c : R, a * (b + c)  = (a * b) + (a * c))
  (pow_one: forall a : R, a^one = a )
  (pow_two: forall a : R, a*a = a^two )
  (char_two : forall a : R, a + a = zero )
  (x y : R)
  : (x + y)^two = (x^two) + y^(two)   := 
  by calc (x + y)^two = (x + y) * (x + y) := by simp [comm_add , comm_mul, add_assoc, mul_assoc, sub_canon, neg_add , div_canon , zero_add, zero_mul, one_mul, distribute, pow_one, pow_two, char_two]
                    _ = (x * (x + y) + y * (x + y)) := by simp [comm_add , comm_mul, add_assoc, mul_assoc, sub_canon, neg_add , div_canon , zero_add, zero_mul, one_mul, distribute, pow_one, pow_two, char_two]
                    _ = (x^two + x * y + y * x + y^two) := by simp [comm_add , comm_mul, add_assoc, mul_assoc, sub_canon, neg_add , div_canon , zero_add, zero_mul, one_mul, distribute, pow_one, pow_two, char_two]
                    _ = (x^two) + (y^two) :=  by simp [comm_add , comm_mul, add_assoc, mul_assoc, sub_canon, neg_add , div_canon , zero_add, zero_mul, one_mul, distribute, pow_one, pow_two, char_two]
   