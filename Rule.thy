theory Rule
  imports Graph
begin

datatype lty = Aty | Ity | Sty | Lty
type_synonym tyenv = "vname \<rightharpoonup> lty"


record ruleschema =
  rule_ty     :: tyenv
  rule_lhs    :: rulegraph
  rule_rhs    :: rulegraph
  rule_interf :: "noderef set"

fun ruleschema_inverse :: "ruleschema \<Rightarrow> ruleschema" where
"ruleschema_inverse r = r\<lparr>rule_lhs := (rule_rhs r), rule_rhs := (rule_lhs r)\<rparr>"


fun wf_ruleschema :: "ruleschema \<Rightarrow> bool" where
"wf_ruleschema r = 
  ( wf_graph (rule_lhs r) 
  \<and> wf_graph (rule_rhs r) 
  \<and> rule_interf r \<subseteq> (dom (nodes (rule_lhs r)))
  \<and> rule_interf r \<subseteq> (dom (nodes (rule_rhs r)))) " 
\<comment> \<open>TODO add var restrictions\<close>






datatype cond = T

type_synonym rule = "ruleschema \<times> cond"

end