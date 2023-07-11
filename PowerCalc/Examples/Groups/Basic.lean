import EggTactic
--import PowerCalc.Tactic
-- Ring axioms
axiom G : Type
axiom G.mul : G → G → G
axiom G.one : G
axiom G.inv : G → G

noncomputable instance : Mul G where
  mul := G.mul

-- this should be done properly by gathering the axioms from tags and/or the environment
set_option hygiene false in
macro "ges" : tactic => `(tactic| egg [assocMul, invLeft, mulOne, oneMul, invRight] noInstantiation (timeLimit := 5))
