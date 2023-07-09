import PowerCalc.Examples.PolynomialsPerformance.Basic

open R in
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
  (pow_two: forall a : R, a*a = a^two)
  (char_two : forall a : R, a + a = zero )
  (x y : R)
  : (x + y)^two = (x^two) + y^(two)   := by
  calc (x + y)^two = (x + y) * (x + y) := by rw [← pow_two]
                 _ = ((x + y) * x) + ((x + y) * y) := by rw [distribute]
                 _ = (x * (x + y)) + ((x + y) * y) := by rw [comm_mul]
                 _ = ((x * x) + (x * y)) + ((x + y) * y) := by rw [distribute]
                 _ = ((x^two) + (x * y)) + ((x + y) * y) := by rw [pow_two]
                 _ = ((x^two) + (x * y)) + (y * (x + y)) := by rw [comm_mul y _]
                 _ = ((x^two) + (x * y)) + ((y * x) + (y * y)) := by rw [distribute]
                 _ = ((x^two) + (x * y)) + ((y * x) + (y^two)) := by rw [pow_two y]
                 _ = ((x^two) + (x * y)) + ((x * y) + (y^two)) := by rw [comm_mul y x]
                 _ = (x^two) + ((x * y) + ((x * y) + (y^two))) := by rw [add_assoc (x^two)]
                 _ = (x^two) + (((x * y) + (x * y)) + (y^two)) := by rw [add_assoc (x * y)]
                 _ = (x^two) + (zero + (y^two)) := by rw [char_two]
                 _ = (x^two) + ((y^two) + zero) := by rw [comm_add zero]
                 _ = (x^two) + (y^two) := by rw [zero_add]
