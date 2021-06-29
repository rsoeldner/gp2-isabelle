theory Com
  imports Rule "HOL-Library.FSet"
begin


datatype com
  = Skip 
  | Break
  | Fail
  | Seq com com ("_ ;; _" 50)
  | If com com com  ("IF _ THEN _ ELSE _")
  | Try com com com ("TRY _ THEN _ ELSE _")
  | Alap com ("_!" [51] 50)
  | Or com com ("_ OR _")
  | RuleSet "rule set"

abbreviation RuleApp where "RuleApp r \<equiv> RuleSet {r}"

(* Definition 48, https://arxiv.org/pdf/2010.14549.pdf *)
fun is_loopfree :: "com \<Rightarrow> bool" where
  "is_loopfree Skip        = True"
| "is_loopfree Break       = True"
| "is_loopfree Fail        = True"
| "is_loopfree (Seq a b)   = (is_loopfree a \<and> is_loopfree b)"
| "is_loopfree (If a b c)  = (is_loopfree a \<and> is_loopfree b \<and> is_loopfree c)"
| "is_loopfree (Try a b c) = (is_loopfree a \<and> is_loopfree b \<and> is_loopfree c)"
| "is_loopfree (Alap _)    = False"
| "is_loopfree (Or a b)    = (is_loopfree a \<and> is_loopfree b)"
| "is_loopfree (RuleSet _) = True"

(* Definition 47, https://arxiv.org/pdf/2010.14549.pdf *)
fun is_nonfailing :: "com \<Rightarrow> bool" where
  "is_nonfailing Skip         = True"
| "is_nonfailing Break        = True"
| "is_nonfailing (RuleSet rs) = (\<forall>(r, _) \<in> rs. (rule_lhs r) = empty_graph)"
| "is_nonfailing (Alap r)     = is_nonfailing r"
| "is_nonfailing (Seq a b)    = (is_nonfailing a \<and> is_nonfailing b)"
| "is_nonfailing (If  _ a b)  = (is_nonfailing a \<and> is_nonfailing b)"
| "is_nonfailing (Try _ a b)  = (is_nonfailing a \<and> is_nonfailing b)"
| "is_nonfailing (Or a b)     = (is_nonfailing a \<and> is_nonfailing b)"
| "is_nonfailing Fail         = False"

(* Definition 48, https://arxiv.org/pdf/2010.14549.pdf *)
fun is_iterprog :: "com \<Rightarrow> bool" where
  "is_iterprog (Seq a b) = (is_loopfree a \<and> is_nonfailing b)"
| "is_iterprog c         = (is_loopfree c \<and> is_nonfailing c)"

(* Definition 50 *)
fun is_ctrlprog :: "com \<Rightarrow> bool" where
  "is_ctrlprog (If  a b c) = (is_loopfree a \<and> is_iterprog b \<and> is_iterprog c)"
| "is_ctrlprog (Try a b c) = (is_loopfree (Seq a b) \<and> is_iterprog c)"
| "is_ctrlprog _           = False"

end