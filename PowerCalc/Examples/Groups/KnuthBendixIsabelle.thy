(*  Title:      HOL/Isar_Examples/Group.thy
    Author:     Makarius
*)

section \<open>Basic group theory\<close>

theory KnuthBendixIsabelle
  imports Main
begin

subsection \<open>Groups and calculational reasoning\<close> 

text \<open>
  Groups over signature \<open>(* :: \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> \<alpha>, 1 :: \<alpha>, inverse :: \<alpha> \<Rightarrow> \<alpha>)\<close> are
  defined as an axiomatic type class as follows. Note that the parent classes
  \<^class>\<open>times\<close>, \<^class>\<open>one\<close>, \<^class>\<open>inverse\<close> is provided by the basic HOL theory.
\<close>

class group = times + one + inverse +
  assumes group_assoc: "(x * y) * z = x * (y * z)"
    and group_left_one: "1 * x = x"
    and group_left_inverse: "inverse x * x = 1"

text \<open>
  The group axioms only state the properties of left one and inverse, the
  right versions may be derived as follows.
\<close>

theorem (in group) group_right_inverse: "x * inverse x = 1"
proof -
  have "x * inverse x = 1 * (x * inverse x)"
    by (simp only: group_left_one)
  also have "\<dots> = 1 * x * inverse x"
    by (simp only: group_assoc)
  also have "\<dots> = inverse (inverse x) * inverse x * x * inverse x"
    by (simp only: group_left_inverse)
  also have "\<dots> = inverse (inverse x) * (inverse x * x) * inverse x"
    by (simp only: group_assoc)
  also have "\<dots> = inverse (inverse x) * 1 * inverse x"
    by (simp only: group_left_inverse)
  also have "\<dots> = inverse (inverse x) * (1 * inverse x)"
    by (simp only: group_assoc)
  also have "\<dots> = inverse (inverse x) * inverse x"
    by (simp only: group_left_one)
  also have "\<dots> = 1"
    by (simp only: group_left_inverse)
  finally show ?thesis .
qed

text \<open>
  With \<open>group_right_inverse\<close> already available, \<open>group_right_one\<close>
  is now established much easier.
\<close>

theorem (in group) group_right_one: "x * 1 = x"
proof -
  have "x * 1 = x * (inverse x * x)"
    by (simp only: group_left_inverse)
  also have "\<dots> = x * inverse x * x"
    by (simp only: group_assoc)
  also have "\<dots> = 1 * x"
    by (simp only: group_right_inverse)
  also have "\<dots> = x"
    by (simp only: group_left_one)
  finally show ?thesis .
qed

text \<open>
  \<^medskip>
  The calculational proof style above follows typical presentations given in
  any introductory course on algebra. The basic technique is to form a
  transitive chain of equations, which in turn are established by simplifying
  with appropriate rules. The low-level logical details of equational
  reasoning are left implicit.

  Note that ``\<open>\<dots>\<close>'' is just a special term variable that is bound
  automatically to the argument\<^footnote>\<open>The argument of a curried infix expression
  happens to be its right-hand side.\<close> of the last fact achieved by any local
  assumption or proven statement. In contrast to \<open>?thesis\<close>, the ``\<open>\<dots>\<close>''
  variable is bound \<^emph>\<open>after\<close> the proof is finished.

  There are only two separate Isar language elements for calculational proofs:
  ``\<^theory_text>\<open>also\<close>'' for initial or intermediate calculational steps, and
  ``\<^theory_text>\<open>finally\<close>'' for exhibiting the result of a calculation. These constructs
  are not hardwired into Isabelle/Isar, but defined on top of the basic
  Isar/VM interpreter. Expanding the \<^theory_text>\<open>also\<close> and \<^theory_text>\<open>finally\<close> derived language
  elements, calculations may be simulated by hand as demonstrated below.
\<close>

theorem (in group) "x * 1 = x"
proof -
  have "x * 1 = x * (inverse x * x)"
    by (simp only: group_left_inverse)

  note calculation = this
    \<comment> \<open>first calculational step: init calculation register\<close>

  have "\<dots> = x * inverse x * x"
    by (simp only: group_assoc)

  note calculation = trans [OF calculation this]
    \<comment> \<open>general calculational step: compose with transitivity rule\<close>

  have "\<dots> = 1 * x"
    by (simp only: group_right_inverse)

  note calculation = trans [OF calculation this]
    \<comment> \<open>general calculational step: compose with transitivity rule\<close>

  have "\<dots> = x"
    by (simp only: group_left_one)

  note calculation = trans [OF calculation this]
    \<comment> \<open>final calculational step: compose with transitivity rule \dots\<close>
  from calculation
    \<comment> \<open>\dots\ and pick up the final result\<close>

  show ?thesis .
qed

text \<open>
  Note that this scheme of calculations is not restricted to plain
  transitivity. Rules like anti-symmetry, or even forward and backward
  substitution work as well. For the actual implementation of \<^theory_text>\<open>also\<close> and
  \<^theory_text>\<open>finally\<close>, Isabelle/Isar maintains separate context information of
  ``transitivity'' rules. Rule selection takes place automatically by
  higher-order unification.
\<close>

subsection \<open>More theorems of group theory\<close>

text \<open>
  The one element is already uniquely determined by preserving an \<^emph>\<open>arbitrary\<close>
  group element.
\<close>



(*
theorem (in group) inv_mul_hammer : "inverse (x * y) = inverse y * inverse x"
proof -
  show ?thesis by (metis local.group_assoc local.group_left_one local.group_right_inverse)
qed

theorem (in group) inv_inv_hammer : "inverse (inverse x) = x"
proof -
  show ?thesis by (metis local.group_assoc local.group_left_inverse local.group_left_one)
qed
*) 

theorem (in group) inv_mul : "inverse (x * y) = inverse y * inverse x"
proof - 
  have "inverse (x * y) = (inverse (x * y)) * (x * (y * inverse y) * (inverse x))" 
    by (simp add: local.group_right_inverse local.group_right_one)
    also have "... = inverse y * inverse x"
    by (metis local.group_assoc local.group_right_inverse local.group_right_one)
    finally show ?thesis .
  qed

theorem (in group) inv_inv: "inverse (inverse x) = x"
proof -
  have "inverse (inverse x) = (inverse (inverse x))*((inverse x) * x)"
  by (simp add: local.group_left_inverse local.group_right_one)
  also have "... = x" 
  by (metis local.group_assoc local.group_left_inverse local.group_left_one) 
    finally show ?thesis .
  qed

end
