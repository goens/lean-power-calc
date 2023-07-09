import EggTactic
-- Ring axioms
axiom R : Type
axiom R.add : R → R → R
axiom R.sub : R → R → R
axiom R.mul : R → R → R
axiom R.div : R → R → R
axiom R.pow : R → R → R
axiom R.zero : R
axiom R.one : R
axiom R.inv : R → R
axiom R.neg : R → R
axiom R.choose : R → R → R
axiom R.factorial : R → R

-- notation
noncomputable instance : Add R where
  add := R.add
noncomputable instance : Sub R where
  sub := R.sub
noncomputable instance : Mul R where
  mul := R.mul
noncomputable instance : Div R where
  div := R.div
noncomputable instance : Pow R R where
  pow := R.pow
notation r "!" => R.factorial r

-- this should be done properly by gathering the axioms from tags and/or the environment
set_option hygiene false in
macro "eggcalc" : tactic => `(tactic| egg [comm_add , comm_mul, add_assoc, mul_assoc, sub_canon, neg_add , div_canon , zero_add, zero_mul, one_mul, distribute, pow_one, pow_two, char_two] simplify (timeLimit := 3601) )

-- adds pow_three
set_option hygiene false in
macro "eggcalc3" : tactic => `(tactic| egg [comm_add , comm_mul, add_assoc, mul_assoc, sub_canon, neg_add , div_canon , zero_add, zero_mul, one_mul, distribute, pow_one, pow_two, char_two, pow_three] simplify (timeLimit := 3601) )
