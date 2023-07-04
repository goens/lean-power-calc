import EggTactic


-- There's a bug in the reconstruction of the proof (or the egg proof code).
-- To test they do all work, however, run: 
-- `lake build PowerCalc.Examples.PolynomialsPerformance.ThreeGuided 2>&1 | rg -i stop_reason`
-- after uncommenting the next line:
-- set_option trace.EggTactic.egg true
theorem freshmans_dream_3
  (R: Type )
  (add: R → R → R )
  (sub: R → R → R )
  (mul: R → R → R )
  (pow: R → R → R )
  (zero : R )
  (one: R )
  (two : R )
  (three : R )
  (four : R )
  (inv : R → R )
  (neg : R → R )
  (comm_add : forall a b : R,  (add a b)        = (add b a) )
  (comm_mul:  forall a b : R, (mul a b)        = (mul b a) )
  (assoc_add: forall a b c : R, (add a (add b c)) = (add (add a b) c) )
  (assoc_mul: forall a b c : R, (mul a (mul b c)) = (mul (mul a b) c) )
  (add_assoc: forall a b c : R, (add (add a b) c) = (add a (add b c)) )
  (mul_assoc: forall a b c : R, (mul (mul a b) c) = (mul a (mul b c)) )
  (sub_canon: forall a b : R, (sub a b) = (add a (mul (neg one) b)) )
  (canon_sub: forall a b : R, (add a (mul (neg one) b)) = (sub a b)  )
  (zero_add: forall a : R, (add a zero) = a )
  (zero_mul: forall a : R, (mul a zero) = zero )
  (one_mul: forall a : R,   (mul a one) = a )
  (add_zero: forall a : R,  a = (add a zero) )
  (mul_one: forall a : R,   a = (mul a one) )
  (cancel_sub: forall a : R,  (sub a a) = zero )
  (distribute: forall a b c : R, (mul a (add b c))        = (add (mul a b) (mul a c)) )
  (factor    : forall a b c : R, (add (mul a b) (mul a c)) = (mul a (add b c)) )
  (pow_mul: forall a b c : R, (mul (pow a b) (pow a c)) = (pow a (add b c)) )
  (pow_one: forall a : R, (pow a one) = a )
  (pow_two: forall a : R, (pow a two) = (mul a a) )
  (pow_three: forall a : R, (pow a three) = (mul a (pow a two)) )
  (pow_four: forall a : R, (pow a four) = (mul (pow a two) (pow a two)) )
  (one_pow: forall a : R, a = (pow a one) )
  (two_pow: forall a : R, (mul a a) = (pow a two) )
  (three_pow: forall a : R, (mul a (pow a two)) = (pow a three) )
  (four_pow: forall a : R, (mul (pow a two) (pow a two)) = (pow a four) )
  (two_add : forall a : R, (add a a) = (mul two a) )
  (add_two : forall a : R, (mul two a) = (add a a) )
  (char_two : forall a : R, (add a a) = zero )
  (x y : R)
  : (pow (add x y) three) = (add (pow x three) (add (mul (pow x two) y) (add (mul x (pow y two)) (pow y three)))) := by calc 
  (pow (add x y) three) = (mul (pow (add x y) two) (add x y)) := by egg [comm_add, comm_mul, assoc_add, assoc_mul, add_assoc, mul_assoc, sub_canon, canon_sub, zero_add, zero_mul, one_mul, add_zero, mul_one, cancel_sub, distribute, factor, pow_mul, pow_one, pow_two, pow_three, pow_four, one_pow, two_pow, three_pow, four_pow, two_add , add_two , char_two] simplify (timeLimit := 999) 
                      _ = mul (mul (add x y) (add x y)) (add x y) := by egg [comm_add, comm_mul, assoc_add, assoc_mul, add_assoc, mul_assoc, sub_canon, canon_sub, zero_add, zero_mul, one_mul, add_zero, mul_one, cancel_sub, distribute, factor, pow_mul, pow_one, pow_two, pow_three, pow_four, one_pow, two_pow, three_pow, four_pow, two_add , add_two , char_two] simplify (timeLimit := 999) 
                      _ = mul (add (add (pow x two) (mul x y)) (add (mul y x) (pow y two))) (add x y) := by egg [comm_add, comm_mul, assoc_add, assoc_mul, add_assoc, mul_assoc, sub_canon, canon_sub, zero_add, zero_mul, one_mul, add_zero, mul_one, cancel_sub, distribute, factor, pow_mul, pow_one, pow_two, pow_three, pow_four, one_pow, two_pow, three_pow, four_pow, two_add , add_two , char_two] simplify (timeLimit := 999) 
                      _ = mul (add (pow x two) (pow y two)) (add x y) :=  by egg [comm_add, comm_mul, assoc_add, assoc_mul, add_assoc, mul_assoc, sub_canon, canon_sub, zero_add, zero_mul, one_mul, add_zero, mul_one, cancel_sub, distribute, factor, pow_mul, pow_one, pow_two, pow_three, pow_four, one_pow, two_pow, three_pow, four_pow, two_add , add_two , char_two] simplify (timeLimit := 999)
                      _ = (add (pow x three) (add (mul (pow x two) y) (add (mul x (pow y two)) (pow y three))))  := by egg [comm_add, comm_mul, assoc_add, assoc_mul, add_assoc, mul_assoc, sub_canon, canon_sub, zero_add, zero_mul, one_mul, add_zero, mul_one, cancel_sub, distribute, factor, pow_mul, pow_one, pow_two, pow_three, pow_four, one_pow, two_pow, three_pow, four_pow, two_add , add_two , char_two] simplify (timeLimit := 999) -- sorry because of bug in transaltion back from egg