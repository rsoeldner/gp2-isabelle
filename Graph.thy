theory Graph
  imports Main Common
begin

type_synonym noderef = nat
type_synonym edgeref = nat

record ('m, 'l) node =
  node_mark   :: 'm
  node_label  :: 'l
  node_rooted :: bool

record ('m, 'l) edge =
  edge_src   :: noderef
  edge_trg   :: noderef
  edge_mark  :: 'm
  edge_label :: 'l
  
record ('nm, 'em, 'l) graph =       
  nodes :: "noderef \<rightharpoonup> ('nm, 'l) node"
  edges :: "edgeref \<rightharpoonup> ('em, 'l) edge"


definition empty_graph :: "('nm, 'em, 'l) graph" where
"empty_graph = \<lparr>nodes = Map.empty, edges = Map.empty\<rparr>"

fun wf_graph :: "('nm, 'em, 'l) graph \<Rightarrow> bool" where
"wf_graph gr = (\<forall>e \<in> dom (edges gr). 
    edge_trg (the (edges gr e)) \<in> dom (nodes gr) \<and> edge_src (the (edges gr e)) \<in> dom (nodes gr))"
(* 
definition ex :: graph where
"ex = \<lparr> nodes = [1 \<mapsto> node, 2 \<mapsto> node]
      , edges = [1 \<mapsto> \<lparr>src = 1, trg = 2\<rparr>, 2 \<mapsto> \<lparr>src = 1, trg = 2\<rparr>]
      \<rparr>"

 *)
fun indeg :: "('nm, 'em, 'l) graph \<Rightarrow> noderef \<Rightarrow> nat" where
"indeg gr n = mfold (edges gr) 
                    (\<lambda>(_,v) b. if edge_trg v = n then Suc b else b)
                    0"

fun outdeg :: "('nm, 'em, 'l) graph \<Rightarrow> noderef \<Rightarrow> nat" where
"outdeg gr n = mfold (edges gr) 
                     (\<lambda>(_,v) b. if edge_src v = n then Suc b else b)
                     0"
(* 
lemma "(indeg ex 2 = 2)"
  by (simp add: ex_def)

lemma "indeg ex 3 = 0"
  by (simp add: ex_def)
 *)

(* 
datatype form = T | F | Conj form form | Indeg noderef nat

find_consts "'a set \<Rightarrow> 'a list"

fun dang :: "graph \<Rightarrow> form" where
"dang gr = (let nrefs = sorted_list_of_set (dom (nodes gr)) in 
  fold (\<lambda>a b. Conj (Indeg a (indeg gr a)) b) nrefs T)"

lemma "dang ex = Conj (Indeg 2 1) (Conj (Indeg 1 0) T)"
  apply (simp add: ex_def)
  apply (intro conjI)
   apply (simp add: Set_filter_fold comp_fun_commute.fold_insert comp_fun_commute_filter_fold)
  by auto

   *)
  
section \<open>Hostgraph\<close>

datatype hostlabel_atom 
  = I int 
  | S string

type_synonym hostlabel 
  = "hostlabel_atom list"

datatype hostmark_node 
  = HostMarkNode_None 
  | HostMarkNode_Red 
  | HostMarkNode_Green 
  | HostMarkNode_Blue
  | HostMarkNode_Grey

datatype hostmark_edge 
  = HostMarkEdge_None 
  | HostMarkEdge_Red 
  | HostMarkEdge_Green 
  | HostMarkEdge_Blue 
  | HostMarkEdge_Dashed

type_synonym hostgraph 
  = "(hostmark_node, hostmark_edge, hostlabel) graph"


section \<open>Rulegraph\<close>

type_synonym vname = string

datatype rulelabel_atom 
  = I int 
  | S string 
  | Var vname
  | Add rulelabel_atom rulelabel_atom
  | Sub rulelabel_atom rulelabel_atom
  | Indeg noderef
  | Outdeg noderef
  | Length rulelabel_atom

type_synonym rulelabel = "rulelabel_atom list"

datatype rulemark_node 
  = RuleMarkNode_None 
  | RuleMarkNode_Red 
  | RuleMarkNode_Green 
  | RuleMarkNode_Blue
  | RuleMarkNode_Grey
  | RuleMarkNode_Any

datatype rulemark_edge 
  = RuleMarkEdge_None 
  | RuleMarkEdge_Red 
  | RuleMarkEdge_Green 
  | RuleMarkEdge_Blue 
  | RuleMarkEdge_Dashed
  | RuleMarkEdge_Any

type_synonym rulegraph = "(rulemark_node, rulemark_edge, rulelabel) graph"


section \<open>Helper\<close>

fun mark_eq_node :: "rulemark_node \<Rightarrow> rulemark_node \<Rightarrow> bool" where
  "mark_eq_node _                  RuleMarkNode_Any = True"
| "mark_eq_node RuleMarkNode_Any   _                = True"
| "mark_eq_node a                  b                = (a = b)"


fun mark_eq_edge :: "rulemark_edge \<Rightarrow> rulemark_edge \<Rightarrow> bool" where
  "mark_eq_edge _                  RuleMarkEdge_Any = True"
| "mark_eq_edge RuleMarkEdge_Any   _                = True"
| "mark_eq_edge a                  b                = (a = b)"

(* 
fun mark_eq_node :: "hostmark_node \<Rightarrow> rulemark_node \<Rightarrow> bool" where
  "mark_eq_node _                  RuleMarkNode_Any   = True"
| "mark_eq_node HostMarkNode_None  RuleMarkNode_None  = True"
| "mark_eq_node HostMarkNode_Red   RuleMarkNode_Red   = True"
| "mark_eq_node HostMarkNode_Green RuleMarkNode_Green = True"
| "mark_eq_node HostMarkNode_Blue  RuleMarkNode_Blue  = True"
| "mark_eq_node HostMarkNode_Grey  RuleMarkNode_Grey  = True"
| "mark_eq_node _                  _                  = False"


fun mark_eq_edge :: "hostmark_edge \<Rightarrow> rulemark_edge \<Rightarrow> bool" where
  "mark_eq_edge _                   RuleMarkEdge_Any    = True"
| "mark_eq_edge HostMarkEdge_None   RuleMarkEdge_None   = True"
| "mark_eq_edge HostMarkEdge_Red    RuleMarkEdge_Red    = True"
| "mark_eq_edge HostMarkEdge_Green  RuleMarkEdge_Green  = True"
| "mark_eq_edge HostMarkEdge_Blue   RuleMarkEdge_Blue   = True"
| "mark_eq_edge HostMarkEdge_Dashed RuleMarkEdge_Dashed = True"
| "mark_eq_edge _                   _                   = False"
 *)


fun conv_mark_node :: "hostmark_node \<Rightarrow> rulemark_node" where
  "conv_mark_node HostMarkNode_None = RuleMarkNode_None"
| "conv_mark_node HostMarkNode_Red = RuleMarkNode_Red"
| "conv_mark_node HostMarkNode_Green = RuleMarkNode_Green"
| "conv_mark_node HostMarkNode_Blue = RuleMarkNode_Blue"
| "conv_mark_node HostMarkNode_Grey = RuleMarkNode_Grey"

fun conv_mark_edge :: "hostmark_edge \<Rightarrow> rulemark_edge" where
  "conv_mark_edge HostMarkEdge_None = RuleMarkEdge_None"
| "conv_mark_edge HostMarkEdge_Red = RuleMarkEdge_Red"
| "conv_mark_edge HostMarkEdge_Green = RuleMarkEdge_Green"
| "conv_mark_edge HostMarkEdge_Blue = RuleMarkEdge_Blue"
| "conv_mark_edge HostMarkEdge_Dashed = RuleMarkEdge_Dashed"

fun conv_label :: "hostlabel \<Rightarrow> rulelabel" where
"conv_label h = map (\<lambda>a. case a of hostlabel_atom.I i \<Rightarrow> I i | hostlabel_atom.S s \<Rightarrow> S s) h"


fun label_is_atom :: "rulelabel \<Rightarrow> bool" where
  "label_is_atom (I _ # []) = True"
| "label_is_atom (S _ # []) = True"
| "label_is_atom _ = False"

end