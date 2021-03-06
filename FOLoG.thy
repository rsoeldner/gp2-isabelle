theory FOLoG
  imports Rule Com Varnames "HOL-Library.AList_Mapping"
begin

\<comment> \<open>quantifier reference\<close>
datatype qref 
  = Nref noderef 
  | Eref edgeref
  | Lref hostlabel

datatype val
  = Val_MarkNode rulemark_node
  | Val_MarkEdge rulemark_edge
  | Val_Label rulelabel
  | Val_Int nat

datatype tm 
  = Term_QVar vname ("\<langle>_\<rangle>" [50] 50)
  | Term_Ref qref
  | Term_Val val
  | Term_Mark tm  ("\<lceil>mark _\<rceil>" [50] 50)
  | Term_Label tm ("\<lceil>label _\<rceil>" [50] 50)
  | Term_Src tm ("\<lceil>src _\<rceil>" [50] 50)
  | Term_Trg tm ("\<lceil>trg _\<rceil>" [50] 50)
  | Term_Indeg  tm ("\<lceil>indeg _\<rceil>"  [50] 50)
  | Term_Outdeg tm ("\<lceil>outdeg _\<rceil>" [50] 50)

abbreviation ref_nref :: "noderef \<Rightarrow> tm" ("\<leadsto>\<^sub>V _" [50] 50) where
"ref_nref nid \<equiv> Term_Ref (Nref nid)"

abbreviation ref_eref :: "noderef \<Rightarrow> tm" ("\<leadsto>\<^sub>E _" [50] 50) where
"ref_eref eid \<equiv> Term_Ref (Eref eid)"

abbreviation val_markv :: "rulemark_node \<Rightarrow> tm" ("\<triangleright>\<^sub>V _" [50] 50) where
"val_markv m \<equiv> Term_Val (Val_MarkNode m)"

abbreviation val_marke :: "rulemark_edge \<Rightarrow> tm" ("\<triangleright>\<^sub>E _" [50] 50) where
"val_marke m \<equiv> Term_Val (Val_MarkEdge m)"

abbreviation val_label :: "rulelabel \<Rightarrow> tm" ("\<triangleright>\<^sub>L _" [50] 50) where
"val_label l \<equiv> Term_Val (Val_Label l)"

abbreviation val_int :: "nat \<Rightarrow> tm" ("\<triangleright>\<^sub>I _" [50] 50) where
"val_int i \<equiv> Term_Val (Val_Int i)"

datatype qty = Edge | Node | Label

datatype form 
  = T 
  | Not form ("\<lceil>\<not>\<rceil> _" [40] 40)
  | Conj form form (infixr "\<lceil>\<and>\<rceil>" 35)
  | Disj form form (infixr "\<lceil>\<or>\<rceil>" 30)
  | Exi vname qty form ("\<lceil>\<exists> _ : _\<rceil> _" [0, 0, 10] 10)
  | Rooted tm ("\<lceil>rooted _\<rceil>" [50] 50)
  | Typed tm lty (infixr "\<lceil>::\<rceil>" 45)
  | Eq tm tm (infixl "\<lceil>=\<rceil>" 40)

fun form_size :: "form \<Rightarrow> nat" where
  "form_size (Not t) = 1 + form_size t"
| "form_size (Conj a b) = 1 + form_size a + form_size b"
| "form_size (Disj a b) = 1 + form_size a + form_size b"
| "form_size (Exi _ _ t) = 1 + form_size t"
| "form_size _ = 0"


abbreviation not_eq :: "tm \<Rightarrow> tm \<Rightarrow> form" (infixl "\<lceil>\<noteq>\<rceil>" 40) where
"not_eq a b \<equiv> \<lceil>\<not>\<rceil>(a \<lceil>=\<rceil> b)"

abbreviation not_true :: form ("F") where
"not_true \<equiv> \<lceil>\<not>\<rceil>T"

abbreviation unrooted :: "tm \<Rightarrow> form" ("\<lceil>unrooted _\<rceil>" [50] 50) where
"unrooted t \<equiv> \<lceil>\<not>\<rceil>\<lceil>rooted t\<rceil>"

abbreviation form_impl :: "form \<Rightarrow> form \<Rightarrow> form" (infixr "\<lceil>\<longrightarrow>\<rceil>" 25) where
"form_impl l r \<equiv> (\<lceil>\<not>\<rceil>l) \<lceil>\<or>\<rceil> r"

abbreviation form_equality :: "form \<Rightarrow> form \<Rightarrow> form" (infixr "\<lceil>\<longleftrightarrow>\<rceil>" 25) where
"form_equality l r \<equiv> (l \<lceil>\<longrightarrow>\<rceil> r) \<lceil>\<and>\<rceil> (r \<lceil>\<longrightarrow>\<rceil> l)"

abbreviation forall_form :: "vname \<Rightarrow> qty \<Rightarrow> form \<Rightarrow> form" ("\<lceil>\<forall> _ : _\<rceil> _" [0, 0, 10] 10) where
"forall_form v q f \<equiv> \<lceil>\<not>\<rceil>(\<lceil>\<exists> v : q\<rceil> (\<lceil>\<not>\<rceil>f))"

type_synonym state = "vname \<Rightarrow> qref"

fun etm :: "hostgraph \<Rightarrow> state \<Rightarrow> tm \<Rightarrow> tm" where
  "etm _ _ (Term_Val v) = Term_Val v"
| "etm _ _ (Term_Ref v) = Term_Ref v"
| "etm _ s (Term_QVar v) = Term_Ref (s v)"

| "etm g s (Term_Mark t) = (case etm g s t of
    Term_Ref (Nref n) \<Rightarrow> Term_Val (Val_MarkNode (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) n)))))
  | Term_Ref (Eref e) \<Rightarrow> Term_Val (Val_MarkEdge (conv_mark_edge (edge_mark (the (Mapping.lookup (edges g) e))))))"

| "etm g s (Term_Label t) = (case etm g s t of
    Term_Ref (Nref n) \<Rightarrow> Term_Val (Val_Label (conv_label (node_label (the (Mapping.lookup (nodes g) n)))))
  | Term_Ref (Eref e) \<Rightarrow> Term_Val (Val_Label (conv_label (edge_label (the (Mapping.lookup (edges g) e))))))"

\<comment> \<open>src and trg\<close>
| "etm g s (Term_Src t) = (case etm g s t of
    Term_Ref (Eref e) \<Rightarrow> Term_Ref (Nref (edge_src (the (Mapping.lookup (edges g) e)))))"
| "etm g s (Term_Trg t) = (case etm g s t of
    Term_Ref (Eref e) \<Rightarrow> Term_Ref (Nref (edge_trg (the (Mapping.lookup (edges g) e)))))"

\<comment> \<open>indegree and outdegree\<close>
| "etm g s (Term_Indeg t) = (case etm g s t of
    Term_Ref (Nref n) \<Rightarrow> Term_Val (Val_Int (indeg g n)))"
| "etm g s (Term_Outdeg t) = (case etm g s t of
    Term_Ref (Nref n) \<Rightarrow> Term_Val (Val_Int (outdeg g n)))"


fun eval :: "hostgraph \<Rightarrow> state \<Rightarrow> form \<Rightarrow> bool" where
  "eval _ _ T           = True"
| "eval g s (Not f)     = (\<not>eval g s f)"
| "eval g s (Conj a b)  = (eval g s a \<and> eval g s b)"
| "eval g s (Disj a b)  = (eval g s a \<or> eval g s b)"

\<comment> \<open>existential quantification\<close>
| "eval g s (Exi v Node  f) = (\<exists>n \<in> Mapping.keys (nodes g). eval g (s(v := Nref n)) f)"
| "eval g s (Exi v Edge  f) = (\<exists>e \<in> Mapping.keys (edges g). eval g (s(v := Eref e)) f)"
| "eval g s (Exi v Label f) = (\<exists>l \<in> UNIV. eval g (s(v := Lref l)) f)"

| "eval g s (Rooted t) = (case etm g s t of
    Term_Ref (Nref n) \<Rightarrow> node_rooted (the (Mapping.lookup (nodes g) n)))"

| "eval g s (Typed t ty) = undefined" \<comment> \<open>just on I and S, ...., or with variables?\<close>

| "eval g s (Eq l r) = (case (etm g s l, etm g s r) of
    (Term_Val (Val_MarkNode l'), Term_Val (Val_MarkNode r')) \<Rightarrow> mark_eq_node l' r'
  | (Term_Val (Val_MarkEdge l'), Term_Val (Val_MarkEdge r')) \<Rightarrow> mark_eq_edge l' r'
  | (l', r') \<Rightarrow> (l' = r'))"


section \<open>Generalized rule schema\<close>

type_synonym grule = "ruleschema \<times> form \<times> form"

\<comment> \<open>TODO: convertion of c to form\<close>
fun rule_to_grule :: "rule \<Rightarrow> grule" ("_\<^sup>\<or>") where
"rule_to_grule (r, c) = (r, T, T)"

section \<open>Example r1 and r2 \<close>
definition r1 :: rule where
"r1 = (\<lparr>rule_ty = Mapping [(0,Lty), (1,Lty),(2,Lty), (3,Ity), (4,Ity)]
      ,rule_lhs = \<lparr>nodes = Mapping
                           [(1, \<lparr>node_mark = RuleMarkNode_None, node_label = [Var 0], node_rooted = False\<rparr>)
                           ,(2, \<lparr>node_mark = RuleMarkNode_None, node_label = [Var 1], node_rooted = False\<rparr>)
                           ,(3, \<lparr>node_mark = RuleMarkNode_None, node_label = [Var 2], node_rooted = False\<rparr>)]
                  ,edges = Mapping
                           [(1, \<lparr>edge_src = 1, edge_trg = 2, edge_mark = RuleMarkEdge_None, edge_label = [Var 3]\<rparr>)
                           ,(2, \<lparr>edge_src = 1, edge_trg = 3, edge_mark = RuleMarkEdge_None, edge_label = [Var 4]\<rparr>)]\<rparr>
      ,rule_rhs = \<lparr>nodes = Mapping
                           [(1, \<lparr>node_mark = RuleMarkNode_Red , node_label = [Var 0], node_rooted = False\<rparr>)
                           ,(2, \<lparr>node_mark = RuleMarkNode_None, node_label = [Var 1], node_rooted = False\<rparr>)]
                  ,edges = Mapping
                          [(1,  \<lparr>edge_src = 1, edge_trg = 2, edge_mark = RuleMarkEdge_None, edge_label = [Add (Var 3) (Var 4)]\<rparr>)]\<rparr>
      ,rule_interf = {1,2}\<rparr>, cond.T)"

definition q1 :: form where
"q1 = (\<lceil>\<not>\<rceil>(\<lceil>\<exists> 0 : Edge\<rceil> \<lceil>mark \<lceil>src \<langle>0\<rangle>\<rceil>\<rceil> \<lceil>\<noteq>\<rceil> \<triangleright>\<^sub>V RuleMarkNode_None))"


definition r2 :: rule where
"r2 = (\<lparr>rule_ty = Mapping [(0, Lty)]
      ,rule_lhs = \<lparr>nodes = Mapping [(1, \<lparr>node_mark = RuleMarkNode_None, node_label = [Var 0], node_rooted = True\<rparr>)]
                  ,edges = Mapping.empty\<rparr>
      ,rule_rhs = \<lparr>nodes = Mapping 
                           [(1, \<lparr>node_mark = RuleMarkNode_None, node_label = [Var 0], node_rooted = False\<rparr>)
                           ,(2, \<lparr>node_mark = RuleMarkNode_None, node_label = [Var 0], node_rooted = True\<rparr>)]
                  ,edges = Mapping [(1, \<lparr>edge_src = 1, edge_trg = 2, edge_mark = RuleMarkEdge_Dashed, edge_label = []\<rparr>)]\<rparr>
      ,rule_interf = {1}\<rparr>, cond.T)"

definition q2 :: form where
"q2 = (\<lceil>\<exists> 0 : Node\<rceil> \<lceil>unrooted \<langle>0\<rangle>\<rceil>)"


section \<open>Term substitution\<close>

fun subst_term_term :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm" where
"subst_term_term i a x = (if i = x then a else case i of
    Term_Mark   t \<Rightarrow> Term_Mark   (subst_term_term t a x)
  | Term_Label  t \<Rightarrow> Term_Label  (subst_term_term t a x)
  | Term_Src    t \<Rightarrow> Term_Src    (subst_term_term t a x)
  | Term_Trg    t \<Rightarrow> Term_Trg    (subst_term_term t a x)
  | Term_Indeg  t \<Rightarrow> Term_Indeg  (subst_term_term t a x)
  | Term_Outdeg t \<Rightarrow> Term_Outdeg (subst_term_term t a x)
  | a \<Rightarrow> a)"


lemma "subst_term_term (\<leadsto>\<^sub>V 1) (\<leadsto>\<^sub>V 2) (\<leadsto>\<^sub>V 1) = (\<leadsto>\<^sub>V 2)"
  by simp


fun subst_term :: "form \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> form" ("_[_'/_]" [19] 20) where
  "subst_term T _ _ = T"
| "subst_term (Not f)      a x = Not (subst_term f a x)"
| "subst_term (Conj l r)   a x = Conj (subst_term l a x) (subst_term r a x)"
| "subst_term (Disj l r )  a x = Disj (subst_term l a x) (subst_term r a x)"

| "subst_term (Exi v ty f) a x = Exi v ty (subst_term f a x)"
\<comment> \<open>subst term\<close>
| "subst_term (Rooted t) a x = Rooted (subst_term_term t a x)"
| "subst_term (Typed t ty) a x = Typed (subst_term_term t a x) ty"
| "subst_term (Eq l r) a x = Eq (subst_term_term l a x) (subst_term_term r a x)"

lemma "((\<leadsto>\<^sub>V 1 \<lceil>=\<rceil> \<leadsto>\<^sub>V 2)[\<leadsto>\<^sub>V 2/\<leadsto>\<^sub>V 1][\<leadsto>\<^sub>V 3/\<leadsto>\<^sub>V 2]) = (\<leadsto>\<^sub>V 3 \<lceil>=\<rceil> \<leadsto>\<^sub>V 3)"
  by simp

lemma form_size_term[simp] :
  "(size (subst_term f a x)) = (size f)"
  apply (induct f rule:form_size.induct)
           apply (simp_all)
  done


section "SLP construction"

subsection \<open>From precondition to left-application condition\<close>

(* Definition 5.1 Condition Dang *)
fun Dang :: "ruleschema \<Rightarrow> form" where
"Dang r = (let vk = Mapping.filter (\<lambda>k v. k \<notin> (rule_interf r)) (nodes (rule_lhs r)) in
  mfold vk (\<lambda>(i, _) a. 
        \<lceil>indeg  \<leadsto>\<^sub>V i\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>I (indeg  (rule_lhs r) i) 
    \<lceil>\<and>\<rceil> \<lceil>outdeg \<leadsto>\<^sub>V i\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>I (outdeg (rule_lhs r) i) \<lceil>\<and>\<rceil> a) T)"

value "Dang (fst r1)"

(* Definition 5.3 Transformation Split *)
fun Split :: "form \<Rightarrow> ruleschema \<Rightarrow> form" where
\<comment> \<open>base case\<close>
  "Split T           _ = T"
| "Split (Typed v ty) _ = (Typed v ty)"
| "Split (Eq a b)   _ = (Eq a b)"
| "Split (Rooted t)   _ = (Rooted t)"

\<comment> \<open>inductive case\<close>
| "Split (Conj a b) r = Conj (Split a r) (Split b r)"
| "Split (Disj a b) r = Disj (Split a r) (Split b r)"
| "Split (Not c)    r = Not (Split c r)"

\<comment> \<open>quantification\<close>
 | "Split (Exi vname Node f) r = 
    ((mfold (nodes (rule_lhs r)) (\<lambda>(i, _) a. (Split (f[\<leadsto>\<^sub>V i/\<langle>vname\<rangle>]) r) \<lceil>\<or>\<rceil> a) F) \<lceil>\<or>\<rceil>
    (\<lceil>\<exists> vname : Node\<rceil> ((mfold (nodes (rule_lhs r)) 
      (\<lambda>(i, _) a. \<langle>vname\<rangle> \<lceil>\<noteq>\<rceil> \<leadsto>\<^sub>V i \<lceil>\<and>\<rceil> a) T) \<lceil>\<and>\<rceil> Split f r)))"

| "Split (Exi vname Edge f) r =
  (let Inc = (mfold (nodes (rule_lhs r)) (\<lambda>(i,_) ia. 
        (mfold (nodes (rule_lhs r)) (\<lambda>(j,_) ja. (\<lceil>src \<langle>vname\<rangle>\<rceil> \<lceil>=\<rceil> \<leadsto>\<^sub>V i \<lceil>\<and>\<rceil> \<lceil>trg \<langle>vname\<rangle>\<rceil> \<lceil>=\<rceil> \<leadsto>\<^sub>V j 
          \<lceil>\<and>\<rceil> Split (f[\<leadsto>\<^sub>V i/\<lceil>src \<langle>vname\<rangle>\<rceil>][\<leadsto>\<^sub>V j/\<lceil>trg \<langle>vname\<rangle>\<rceil>]) r) \<lceil>\<or>\<rceil> ja) F)
    
      \<lceil>\<or>\<rceil> (\<lceil>src \<langle>vname\<rangle>\<rceil> \<lceil>=\<rceil> \<leadsto>\<^sub>V i \<lceil>\<and>\<rceil> mfold (nodes (rule_lhs r)) (\<lambda>(j,_) ja. \<lceil>trg \<langle>vname\<rangle>\<rceil> \<lceil>\<noteq>\<rceil> \<leadsto>\<^sub>V j \<lceil>\<and>\<rceil> ja) T 
          \<lceil>\<and>\<rceil> Split (f[\<leadsto>\<^sub>V i/\<lceil>src \<langle>vname\<rangle>\<rceil>]) r)
    
      \<lceil>\<or>\<rceil> (mfold (nodes (rule_lhs r)) (\<lambda>(j,_) ja. \<lceil>src \<langle>vname\<rangle>\<rceil> \<lceil>\<noteq>\<rceil> \<leadsto>\<^sub>V j \<lceil>\<and>\<rceil> ja) T
          \<lceil>\<and>\<rceil> \<lceil>trg \<langle>vname\<rangle>\<rceil> \<lceil>=\<rceil> \<leadsto>\<^sub>V i \<lceil>\<and>\<rceil> Split (f[\<leadsto>\<^sub>V i/\<lceil>trg \<langle>vname\<rangle>\<rceil>]) r)
    
      \<lceil>\<or>\<rceil> ia) F) 
   \<lceil>\<or>\<rceil> ((mfold (nodes (rule_lhs r)) (\<lambda>(i,_) ia. \<lceil>src \<langle>vname\<rangle>\<rceil> \<lceil>\<noteq>\<rceil> \<leadsto>\<^sub>V i \<lceil>\<and>\<rceil> ia) T)
        \<lceil>\<and>\<rceil> (mfold (nodes (rule_lhs r)) (\<lambda>(j,_) ja. \<lceil>trg \<langle>vname\<rangle>\<rceil> \<lceil>\<noteq>\<rceil> \<leadsto>\<^sub>V j \<lceil>\<and>\<rceil> ja) T)
        \<lceil>\<and>\<rceil> Split f r)
  in
  ((mfold (edges (rule_lhs r)) (\<lambda>(i, _) a. Split (f[\<leadsto>\<^sub>E i/\<langle>vname\<rangle>]) r \<lceil>\<or>\<rceil> a) F) \<lceil>\<or>\<rceil>
    (\<lceil>\<exists> vname : Edge\<rceil> ((mfold (edges (rule_lhs r)) 
      (\<lambda>(i, _) a. \<langle>vname\<rangle> \<lceil>\<noteq>\<rceil> \<leadsto>\<^sub>E i  \<lceil>\<and>\<rceil> a) T) \<lceil>\<and>\<rceil> Inc))))"

 | "Split (Exi vname Label f) r = Exi vname Label (Split f r)"

value "Split q1 (fst r1)"

(* Definition 5.5 Valuation of c *)
fun Val_Term :: "tm \<Rightarrow> ruleschema \<Rightarrow> tm" where
  "Val_Term (Term_Mark (Term_Ref (Nref n))) r = (Term_Val (Val_MarkNode (node_mark (the (Mapping.lookup (nodes (rule_lhs r)) n)))))"
| "Val_Term (Term_Mark (Term_Ref (Eref e))) r = (Term_Val (Val_MarkEdge (edge_mark (the (Mapping.lookup (edges (rule_lhs r)) e)))))"
| "Val_Term (Term_Mark (Term_Src (Term_Ref (Eref e)))) r =
  (Term_Val (Val_MarkNode (node_mark (the (Mapping.lookup (nodes (rule_lhs r)) (edge_src (the (Mapping.lookup (edges (rule_lhs r)) e))))))))"
| "Val_Term (Term_Mark (Term_Trg (Term_Ref (Eref e)))) r = 
  (Term_Val (Val_MarkNode (node_mark (the (Mapping.lookup (nodes (rule_lhs r)) (edge_trg (the (Mapping.lookup (edges (rule_lhs r)) e))))))))"
| "Val_Term t r = t"

fun Val :: "form \<Rightarrow> ruleschema \<Rightarrow> form" where
  "Val T           _ = T"
| "Val (Typed v ty) _ = (Typed v ty)"

\<comment> \<open>Check again B(x) for rooted, true if v \<in> rule_lhs otherwise false\<close>
| "Val (Rooted (Term_Ref (Nref n))) r = (case Mapping.lookup (nodes (rule_lhs r)) n of
    None \<Rightarrow> F
  | Some n' \<Rightarrow> if node_rooted n' then T else F)"
| "Val (Rooted t) _ = Rooted t"

| "Val (Eq a b)   r = (Eq (Val_Term a r) (Val_Term b r))"

\<comment> \<open>inductive case\<close>
| "Val (Conj a b) r = Conj (Val a r) (Val b r)"
| "Val (Disj a b) r = Disj (Val a r) (Val b r)"
| "Val (Not c)    r = Not (Val c r)"

| "Val (Exi vname ty f) r = Exi vname ty (Val f r)"


(* Definition 5.7 Transformation Lift *)
fun Lift :: "form \<Rightarrow> grule \<Rightarrow> form" where
"Lift c (r, acL, _) = Val (Split (c \<lceil>\<and>\<rceil> acL) r \<lceil>\<and>\<rceil> Dang r) r"




subsection \<open>From left application condition to right application condition\<close>

(* Definition 5.9 Adjustment *)
fun Adj :: "form \<Rightarrow> ruleschema \<Rightarrow> form" where
  "Adj T _ = T"
| "Adj (Not c) r = Not (Adj c r)"
| "Adj (Conj a b) r = Conj (Adj a r) (Adj b r)"
| "Adj (Disj a b) r = Disj (Adj a r) (Adj b r)"


| "Adj (Exi vname Node c) r = 
   (let vk = Mapping.filter (\<lambda>k v. k \<notin> (rule_interf r)) (nodes (rule_rhs r)) ;
        f = mfold vk (\<lambda>(i,_) a. \<langle>vname\<rangle> \<lceil>\<noteq>\<rceil> \<leadsto>\<^sub>V i \<lceil>\<and>\<rceil> a) T
   in Exi vname Node (f \<lceil>\<and>\<rceil> Adj c r))"

  \<comment> \<open>Note: what does R-K reflect for edges?\<close>
(* | "Adj (Exi vname Edge c) r = Exi vname Edge (Adj c r)" *)
| "Adj (Exi vname Edge c) r =
   (let vk = Mapping.filter (\<lambda>_ v. edge_src v \<notin> (rule_interf r) 
                                \<and>  edge_trg v \<notin> (rule_interf r)) (edges (rule_rhs r)) ;
        f = mfold vk (\<lambda>(i,_) a. \<langle>vname\<rangle> \<lceil>\<noteq>\<rceil> \<leadsto>\<^sub>E i \<lceil>\<and>\<rceil> a) T
   in Exi vname Edge (f \<lceil>\<and>\<rceil> Adj c r))"


| "Adj (Exi vname Label c) r = Exi vname Label (Adj c r)"
| "Adj (Rooted t) _ = Rooted t"
| "Adj (Typed t ty) _ = Typed t ty"

\<comment> \<open>Check equal case, a \<in> VL - VL \<union> EL TODO: adjust c' by replacing incon...\<close>
| "Adj (Eq a b) r = (case (a,b) of
    _ \<Rightarrow> Eq a b)"

(* Definition 3.23 Specifying a totally labelled graph *)
fun Spec :: "rulegraph \<Rightarrow> tyenv \<Rightarrow> form" where
"Spec g ty = 
   (let n = mfold (nodes g) (\<lambda>(i,v) a.  
                \<lceil>mark \<leadsto>\<^sub>V i\<rceil>  \<lceil>=\<rceil> \<triangleright>\<^sub>V (node_mark v)
            \<lceil>\<and>\<rceil> (if (node_rooted v) then \<lceil>rooted  \<leadsto>\<^sub>V i\<rceil> else \<lceil>unrooted  \<leadsto>\<^sub>V i\<rceil>)
            \<lceil>\<and>\<rceil> a) T;
       e = mfold (edges g) (\<lambda>(i,v) a.
                \<lceil>src \<leadsto>\<^sub>E i\<rceil>   \<lceil>=\<rceil> \<leadsto>\<^sub>V (edge_src v)
            \<lceil>\<and>\<rceil> \<lceil>trg \<leadsto>\<^sub>E i\<rceil>   \<lceil>=\<rceil> \<leadsto>\<^sub>V (edge_trg v)
            \<lceil>\<and>\<rceil> \<lceil>mark \<leadsto>\<^sub>E i\<rceil>  \<lceil>=\<rceil> \<triangleright>\<^sub>E (edge_mark v)
            \<lceil>\<and>\<rceil> a) T
  in n \<lceil>\<and>\<rceil> e)"
(* "Spec g ty = 
   (let n = mfold (nodes g) (\<lambda>(i,v) a. 
                \<lceil>label \<leadsto>\<^sub>V i\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>L (node_label v) 
            \<lceil>\<and>\<rceil> \<lceil>mark \<leadsto>\<^sub>V i\<rceil>  \<lceil>=\<rceil> \<triangleright>\<^sub>V (node_mark v)
            \<lceil>\<and>\<rceil> (if (node_rooted v) then \<lceil>rooted  \<leadsto>\<^sub>V i\<rceil> else \<lceil>unrooted  \<leadsto>\<^sub>V i\<rceil>)
            \<lceil>\<and>\<rceil> a) T;
       e = mfold (edges g) (\<lambda>(i,v) a.
                \<lceil>src \<leadsto>\<^sub>E i\<rceil>   \<lceil>=\<rceil> \<leadsto>\<^sub>V (edge_src v)
            \<lceil>\<and>\<rceil> \<lceil>trg \<leadsto>\<^sub>E i\<rceil>   \<lceil>=\<rceil> \<leadsto>\<^sub>V (edge_trg v)
            \<lceil>\<and>\<rceil> \<lceil>label \<leadsto>\<^sub>E i\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>L (edge_label v)
            \<lceil>\<and>\<rceil> \<lceil>mark \<leadsto>\<^sub>E i\<rceil>  \<lceil>=\<rceil> \<triangleright>\<^sub>E (edge_mark v)
            \<lceil>\<and>\<rceil> a) T
  in n \<lceil>\<and>\<rceil> e)" *)

(* Definition 5.12 Shifting *)
fun Shift :: "grule \<Rightarrow> form" where
"Shift (r, acl, acr) = (Adj acl r \<lceil>\<and>\<rceil> acr \<lceil>\<and>\<rceil> Spec (rule_rhs r) (rule_ty r) \<lceil>\<and>\<rceil>
                           Dang (ruleschema_inverse r))"

subsection \<open>From rigth application condition to postcondition\<close>

fun fconst :: "form \<Rightarrow> tm list" where
  "fconst T = []"
| "fconst (Not f) = fconst f"
| "fconst (Conj a b) = fconst a @ fconst b"
| "fconst (Disj a b) = fconst a @ fconst b"
| "fconst (Exi _ _ f) = fconst f"
| "fconst (Rooted tm) = (case tm of
    Term_Ref (Nref nid) \<Rightarrow> [Term_Ref (Nref nid)]
    | _ \<Rightarrow> [])"

| "fconst (Typed _ _) = []"
| "fconst (Eq a b) = (let f = (\<lambda>v. case v of
    Term_Ref (Nref nid) \<Rightarrow> [Term_Ref (Nref nid)]
  | Term_Ref (Eref eid) \<Rightarrow> [Term_Ref (Eref eid)]
  | _ \<Rightarrow> []) in f a @ f b)"



fun qconst :: "form \<Rightarrow> vname set" where
  "qconst T = {}"
| "qconst (Not f) = qconst f"
| "qconst (Conj a b) = qconst a \<union> qconst b"
| "qconst (Disj a b) = qconst a \<union> qconst b"
| "qconst (Exi v _ f) = {v} \<union> qconst f"
| "qconst _ = {}"



(* Definition 5.14 Formula Post and Definition 3.25 Variablisation of a condition over a graph *)
fun Post :: "form \<Rightarrow> form" where
"Post f = (let 
  usedvars = qconst f;
  (xs, _) = zipFresh (remdups (fconst f)) usedvars;
  (nids, eids) = partition (\<lambda>(t, _). case t of Term_Ref (Nref n) \<Rightarrow> True | _ \<Rightarrow> False) xs;
  cn = foldr (\<lambda>(ref, vn) a. a[\<langle>vn\<rangle>/ref]) nids f;
  ce = foldr (\<lambda>(ref, vn) a. a[\<langle>vn\<rangle>/ref]) eids cn;
  uniqn= foldr (\<lambda>(x,y) a. \<langle>x\<rangle> \<lceil>\<noteq>\<rceil> \<langle>y\<rangle> \<lceil>\<and>\<rceil> a) [(x,y) . (_, x) \<leftarrow> nids, (_, y) \<leftarrow> nids, x \<noteq> y] T;
  uniqe= foldr (\<lambda>(x,y) a. \<langle>x\<rangle> \<lceil>\<noteq>\<rceil> \<langle>y\<rangle> \<lceil>\<and>\<rceil> a) [(x,y) . (_, x) \<leftarrow> eids, (_, y) \<leftarrow> eids, x \<noteq> y] T;
  qe = foldr (\<lambda>(_,v) a. \<lceil>\<exists> v: Edge\<rceil> a) eids (uniqn \<lceil>\<and>\<rceil> uniqe \<lceil>\<and>\<rceil> ce);
  qn = foldr (\<lambda>(_,v) a. \<lceil>\<exists> v: Node\<rceil> a) nids qe
  in qn)"

fun Slp where
"Slp c r = Post (Shift (fst r, Lift c (r\<^sup>\<or>), T))"


\<comment> \<open>Dang(r1) = indeg(3) = 1 \<and> outdeg(3) = 0\<close>
value "Dang (fst r1)"
lemma "(eval g undefined (Dang (fst r1))) = eval g undefined (\<lceil>indeg  \<leadsto>\<^sub>V 3\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>I 1 \<lceil>\<and>\<rceil> \<lceil>outdeg  \<leadsto>\<^sub>V 3\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>I 0)"
  apply code_simp
  by simp

  
lemma "eval g undefined ((Dang (fst r1)) \<lceil>\<longleftrightarrow>\<rceil> (\<lceil>indeg  \<leadsto>\<^sub>V 3\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>I 1 \<lceil>\<and>\<rceil> \<lceil>outdeg  \<leadsto>\<^sub>V 3\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>I 0))"
  apply code_simp
  apply(simp add: r1_def)
  by (metis (no_types, lifting) foldr_conv_fold gr0I)
  
lemma "eval g undefined (Dang (fst r2))"
  by (code_simp)



lemma "wf_ruleschema (fst r1)" by (simp add: r1_def)
lemma "wf_ruleschema (fst r2)" by (simp add: r2_def)



\<comment> \<open>Example 6 (Transformation Split)\<close> 

lemma "eval g undefined (Split q1 (fst r1) \<lceil>\<longleftrightarrow>\<rceil> (\<lceil>\<not>\<rceil> Split (\<lceil>\<exists> 0 : Edge\<rceil> (\<lceil>mark \<lceil>src \<langle>0\<rangle>\<rceil>\<rceil> \<lceil>\<noteq>\<rceil> \<triangleright>\<^sub>V RuleMarkNode_None)) (fst r1)))"
  by (metis Split.simps(7) eval.simps(2) eval.simps(3) eval.simps(4) q1_def)

 
(* lemma split_q1_r1[simp]: "\<lbrakk> wf_graph g; wf_ruleschema (fst r1)\<rbrakk> \<Longrightarrow> eval g undefined (Split q1 (fst r1) \<lceil>\<longleftrightarrow>\<rceil>
  (\<lceil>\<not>\<rceil>(\<lceil>mark \<lceil>src \<leadsto>\<^sub>E 1\<rceil>\<rceil> \<lceil>\<noteq>\<rceil> \<triangleright>\<^sub>V RuleMarkNode_None \<lceil>\<or>\<rceil>
       \<lceil>mark \<lceil>src \<leadsto>\<^sub>E 2\<rceil>\<rceil> \<lceil>\<noteq>\<rceil> \<triangleright>\<^sub>V RuleMarkNode_None \<lceil>\<or>\<rceil>
        (\<lceil>\<exists> 0 : Edge\<rceil> (\<langle>0\<rangle> \<lceil>\<noteq>\<rceil> \<leadsto>\<^sub>E 1 \<lceil>\<and>\<rceil> \<langle>0\<rangle> \<lceil>\<noteq>\<rceil> \<leadsto>\<^sub>E 2 \<lceil>\<and>\<rceil>
          ((\<lceil>src \<langle>0\<rangle>\<rceil> \<lceil>=\<rceil> \<leadsto>\<^sub>V 1 \<lceil>\<and>\<rceil> \<lceil>mark \<leadsto>\<^sub>V 1\<rceil> \<lceil>\<noteq>\<rceil> \<triangleright>\<^sub>V RuleMarkNode_None)
          \<lceil>\<or>\<rceil> (\<lceil>src \<langle>0\<rangle>\<rceil> \<lceil>=\<rceil> \<leadsto>\<^sub>V 2 \<lceil>\<and>\<rceil> \<lceil>mark \<leadsto>\<^sub>V 2\<rceil> \<lceil>\<noteq>\<rceil> \<triangleright>\<^sub>V RuleMarkNode_None)
          \<lceil>\<or>\<rceil> (\<lceil>src \<langle>0\<rangle>\<rceil> \<lceil>=\<rceil> \<leadsto>\<^sub>V 3 \<lceil>\<and>\<rceil> \<lceil>mark \<leadsto>\<^sub>V 3\<rceil> \<lceil>\<noteq>\<rceil> \<triangleright>\<^sub>V RuleMarkNode_None)
          \<lceil>\<or>\<rceil> (\<lceil>src \<langle>0\<rangle>\<rceil> \<lceil>\<noteq>\<rceil> \<leadsto>\<^sub>V 1 \<lceil>\<and>\<rceil> \<lceil>src \<langle>0\<rangle>\<rceil> \<lceil>\<noteq>\<rceil> \<leadsto>\<^sub>V 2 \<lceil>\<and>\<rceil>
            \<lceil>src \<langle>0\<rangle>\<rceil> \<lceil>\<noteq>\<rceil> \<leadsto>\<^sub>V 3 \<lceil>\<and>\<rceil> \<lceil>mark \<lceil>src \<langle>0\<rangle>\<rceil>\<rceil> \<lceil>\<noteq>\<rceil> \<triangleright>\<^sub>V RuleMarkNode_None)))))))"
  apply (code_simp)
  apply auto
  apply(simp_all add: r1_def q1_def)
  apply (rule conjI)
   apply (rule impI)+
  apply (simp add: dom_def)
  apply (drule spec)
   apply (metis (no_types, lifting))
  apply (simp add: dom_def)
  by blast
 *)

lemma "\<lbrakk> wf_graph g; wf_ruleschema (fst r2)\<rbrakk> \<Longrightarrow> eval g undefined ((Split q2 (fst r2)) \<lceil>\<longleftrightarrow>\<rceil> 
  (\<lceil>unrooted \<leadsto>\<^sub>V 1\<rceil> \<lceil>\<or>\<rceil> (\<lceil>\<exists> 0 : Node\<rceil> (\<langle>0\<rangle> \<lceil>\<noteq>\<rceil> \<leadsto>\<^sub>V 1 \<lceil>\<and>\<rceil> \<lceil>unrooted \<langle>0\<rangle>\<rceil>))))"
  apply code_simp
  by auto  
  

lemma "eval g undefined (\<triangleright>\<^sub>V RuleMarkNode_None \<lceil>\<noteq>\<rceil> \<triangleright>\<^sub>V RuleMarkNode_None) \<Longrightarrow> False"
  by simp

lemma "eval g undefined ((Val (Split q1 (fst r1)) (fst r1))  \<lceil>\<longrightarrow>\<rceil> 
  (\<lceil>\<not>\<rceil>(\<lceil>\<exists>x : Edge\<rceil> (\<langle>x\<rangle> \<lceil>\<noteq>\<rceil> \<leadsto>\<^sub>E 1 \<lceil>\<and>\<rceil> \<langle>x\<rangle> \<lceil>\<noteq>\<rceil> \<leadsto>\<^sub>E 2 \<lceil>\<and>\<rceil>
        \<lceil>src \<langle>x\<rangle>\<rceil> \<lceil>\<noteq>\<rceil> \<leadsto>\<^sub>V 1 \<lceil>\<and>\<rceil> \<lceil>src \<langle>x\<rangle>\<rceil> \<lceil>\<noteq>\<rceil> \<leadsto>\<^sub>V 2 \<lceil>\<and>\<rceil> \<lceil>src \<langle>x\<rangle>\<rceil> \<lceil>\<noteq>\<rceil> \<leadsto>\<^sub>V 3 \<lceil>\<and>\<rceil> \<lceil>mark \<lceil>src \<langle>x\<rangle>\<rceil>\<rceil> \<lceil>\<noteq>\<rceil> \<triangleright>\<^sub>V RuleMarkNode_None))))"
  apply code_simp
  by auto

 
lemma "\<lbrakk> wf_graph g; wf_ruleschema (fst r1)\<rbrakk> \<Longrightarrow> eval g undefined (Val (Split q1 (fst r1)) (fst r1)  \<lceil>\<longleftrightarrow>\<rceil>  
  (\<lceil>\<not>\<rceil> (\<lceil>\<exists> x : Edge\<rceil> (\<langle>x\<rangle> \<lceil>\<noteq>\<rceil> \<leadsto>\<^sub>E 1 \<lceil>\<and>\<rceil> \<langle>x\<rangle> \<lceil>\<noteq>\<rceil> \<leadsto>\<^sub>E 2 \<lceil>\<and>\<rceil>
    (\<lceil>src \<langle>x\<rangle>\<rceil> \<lceil>\<noteq>\<rceil> \<leadsto>\<^sub>V 1 \<lceil>\<and>\<rceil> \<lceil>src \<langle>x\<rangle>\<rceil> \<lceil>\<noteq>\<rceil> \<leadsto>\<^sub>V 2 \<lceil>\<and>\<rceil> \<lceil>src \<langle>x\<rangle>\<rceil> \<lceil>\<noteq>\<rceil> \<leadsto>\<^sub>V 3 \<lceil>\<and>\<rceil> 
     \<lceil>mark \<lceil>src \<langle>x\<rangle>\<rceil>\<rceil> \<lceil>\<noteq>\<rceil> \<triangleright>\<^sub>V RuleMarkNode_None)))))"
  apply code_simp
  by auto
                                    
lemma "eval g undefined (Val (Split q2 (fst r2)) (fst r2) \<lceil>\<longleftrightarrow>\<rceil>  
  (\<lceil>\<exists> x : Node\<rceil> (\<langle>x\<rangle> \<lceil>\<noteq>\<rceil> \<leadsto>\<^sub>V 1 \<lceil>\<and>\<rceil> \<lceil>unrooted \<langle>x\<rangle>\<rceil>)))"
  apply code_simp
  by auto



(* Definition 45 *)
(* \<comment> \<open>Missing condition, add Dang \<lceil>\<and>\<rceil> condition\<close>
fun App :: "rule \<Rightarrow> form" where
"App (rs, c) = Var1 (Spec (rule_lhs rs) (rule_ty rs) \<lceil>\<and>\<rceil> (Dang rs))"
 *)


(* Definition 46 *)
(* function (sequential) 
      Slp     :: "form \<Rightarrow> com \<Rightarrow> form"
  and Pre     :: "com \<Rightarrow> form \<Rightarrow> form"
  and Success :: "com \<Rightarrow> form" 
  and Fail    :: "com \<Rightarrow> form"
  where
  "Slp c (RuleSet rs) = foldr (\<lambda>a b. Post c (a\<^sup>\<or>) \<lceil>\<or>\<rceil> b) (set_to_list rs) F"
| "Pre (RuleSet rs) c = T"            
| "Success (RuleSet rs) = foldr (\<lambda>a b. (App a) \<lceil>\<or>\<rceil> b) (set_to_list rs) F"
| "Fail (RuleSet rs) = (\<lceil>\<not>\<rceil> (Success (RuleSet rs)))" 

| "Slp c (P OR Q) = (Slp c P \<lceil>\<or>\<rceil> Slp c Q)"
| "Pre (P OR Q) c = (Pre P c \<lceil>\<or>\<rceil> Pre Q c)"
| "Success (P OR Q) = (Success P \<lceil>\<or>\<rceil> Success Q)"
| "Fail (P OR Q) = (Fail P \<lceil>\<or>\<rceil> Success Q)"

| "Slp c (P ;; Q) = Slp (Slp c P) Q"
| "Pre (P ;; Q) c = Pre P (Pre Q c)"
| "Success (P ;; Q) = Pre P (Success Q)"
| "Fail (P ;; Q) = (Fail P \<lceil>\<or>\<rceil> Pre P (Fail Q))"

| "Slp c (IF C THEN P ELSE Q) = (Slp (c \<lceil>\<and>\<rceil> Success C) P \<lceil>\<or>\<rceil> Slp (c \<lceil>\<and>\<rceil> Fail C) Q)"
| "Pre (IF C THEN P ELSE Q) c = ((Success C \<lceil>\<and>\<rceil> Pre P c) \<lceil>\<or>\<rceil> (Fail C \<lceil>\<and>\<rceil> Pre Q c))"
| "Success (IF C THEN P ELSE Q) = ((Success C \<lceil>\<and>\<rceil> Success P) \<lceil>\<or>\<rceil> (Fail C \<lceil>\<and>\<rceil> Success Q))"
| "Fail (IF C THEN P ELSE Q) = ((Success C \<lceil>\<and>\<rceil> Fail P) \<lceil>\<or>\<rceil> (Fail C \<lceil>\<and>\<rceil> Fail Q))"


| "Slp c (TRY C THEN P ELSE Q) = ((Slp (c \<lceil>\<and>\<rceil> Success C) (C ;; P)) \<lceil>\<or>\<rceil> Slp (c \<lceil>\<and>\<rceil> Fail C) Q)"
| "Pre (TRY C THEN P ELSE Q) c = ((Pre C (Pre P c)) \<lceil>\<or>\<rceil> (Fail C \<lceil>\<and>\<rceil> Pre Q c))"
| "Success (TRY C THEN P ELSE Q) = (Pre C (Success P) \<lceil>\<or>\<rceil> (Fail C \<lceil>\<and>\<rceil> Success Q))"
| "Fail (TRY C THEN P ELSE Q) = (Pre C (Fail P) \<lceil>\<or>\<rceil> (Fail C \<lceil>\<and>\<rceil> Fail Q))"

| "Slp _ _ = F"
| "Pre _ _ = F"
| "Success _ = F"
| "Fail _ = undefined"
  by pat_completeness auto termination by size_change
 *) 
(* Definition 43 *)
(* fun Break :: "form \<Rightarrow> com \<Rightarrow> form \<Rightarrow> form" where
"Break _ _ _ = T"
 *)

(* 
(* Lemma 17 *)
fun Wlp :: "rule \<Rightarrow> form \<Rightarrow> form" where
"Wlp r d = (\<lceil>\<not>\<rceil>(Slp (\<lceil>\<not>\<rceil>d) (RuleApp r)))"
 *)
(*
inductive 
  hoare :: "form \<Rightarrow> com \<Rightarrow> form \<Rightarrow> bool" ("\<turnstile> ({(1_)}/ (_)/ {(1_)})" 51)
where
  Ruleapp_slp: "\<turnstile> {c} RuleApp r {Slp c (RuleSet {r})}" |

  Ruleapp_wlp: "\<turnstile> {Wlp r d} RuleApp r {d}" |

  Ruleset: "\<lbrakk>\<forall>r \<in> rs. \<turnstile> {c} RuleApp r {d}\<rbrakk> 
            \<Longrightarrow> \<turnstile> {c} RuleSet rs {d}" |

  Skip: "\<turnstile> {c} Skip {c}" |

  Comp: "\<lbrakk>\<turnstile> {c} P {e}; \<turnstile> {e} Q {d} \<rbrakk> 
         \<Longrightarrow> \<turnstile> {c} P;;Q {d}" |

  Cons: "\<lbrakk>\<turnstile> {c'} P {d'}; eval g undefined (c \<lceil>\<longrightarrow>\<rceil> c');  eval g undefined (d' \<lceil>\<longrightarrow>\<rceil> d)\<rbrakk> 
         \<Longrightarrow> \<turnstile> {c} P {d}" |

  If: "\<lbrakk>\<turnstile> {c \<lceil>\<and>\<rceil> Success C} P {d}; \<turnstile> {c \<lceil>\<and>\<rceil> Fail C} Q {d}\<rbrakk>
       \<Longrightarrow> \<turnstile> {c} IF C THEN P ELSE Q {d}" |

  Try: "\<lbrakk> \<turnstile> {c \<lceil>\<and>\<rceil> Success C} C;;P {d}; \<turnstile> {c \<lceil>\<and>\<rceil> Fail C} Q {d}\<rbrakk>
        \<Longrightarrow> \<turnstile> {c} TRY C THEN P ELSE Q {d}" |

  Alap: "\<lbrakk>\<turnstile> {c} C {c}; eval g undefined (Break c C d)\<rbrakk> 
         \<Longrightarrow> \<turnstile> {c} C! {(c \<lceil>\<and>\<rceil> Fail C) \<lceil>\<or>\<rceil> d}" *)

end