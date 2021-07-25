theory TwoColouringEx
  imports Rule FOLoG
begin

abbreviation cast_ruleschema_rule :: "ruleschema \<Rightarrow> rule" where
"cast_ruleschema_rule rs \<equiv> (rs, cond.T)"

declare [[coercion_enabled]]
declare [[coercion cast_ruleschema_rule]]



definition init :: ruleschema where
"init = \<lparr>rule_ty = Mapping [(0,Lty)],
         rule_lhs = \<lparr>nodes = Mapping [(1, \<lparr>node_mark = RuleMarkNode_None, node_label= Var 0 # [], node_rooted=False\<rparr>)]
                   ,edges = Mapping.empty\<rparr>,
         rule_rhs = \<lparr>nodes = Mapping [(1, \<lparr>node_mark = RuleMarkNode_Red, node_label= Var 0 # [] , node_rooted=False\<rparr>)]
               ,edges = Mapping.empty\<rparr>,
         rule_interf = {1}\<rparr>"

definition unmark :: rule where
"unmark = (\<lparr>rule_ty = Mapping [(0, Lty)],
           rule_lhs = \<lparr>nodes = Mapping [(1, \<lparr>node_mark = RuleMarkNode_Any, node_label= Var 0 # [] , node_rooted=False\<rparr>)]
                 ,edges = Mapping.empty\<rparr>,
           rule_rhs = \<lparr>nodes = Mapping[(1, \<lparr>node_mark = RuleMarkNode_None, node_label= Var 0 # [], node_rooted=False\<rparr>)]
                 ,edges = Mapping.empty\<rparr>,
           rule_interf = {1}\<rparr>, cond.T)"

definition col_blue_1 :: ruleschema where
"col_blue_1 = \<lparr>rule_ty = Mapping [(0, Lty), (1, Lty), (2, Lty)]
            ,rule_lhs = \<lparr>nodes = Mapping
                                 [(1, \<lparr>node_mark = RuleMarkNode_Red , node_label = [Var 0], node_rooted = False\<rparr>)
                                 ,(2, \<lparr>node_mark = RuleMarkNode_None, node_label = [Var 1], node_rooted = False\<rparr>)]
                        ,edges = Mapping [(1, \<lparr>edge_src = 1, edge_trg = 2, edge_mark = RuleMarkEdge_None, edge_label = [Var 2]\<rparr>)]\<rparr>
            ,rule_rhs = \<lparr>nodes = Mapping
                                 [(1, \<lparr>node_mark = RuleMarkNode_Red , node_label = [Var 0], node_rooted = False\<rparr>)
                                 ,(2, \<lparr>node_mark = RuleMarkNode_Blue, node_label = [Var 1], node_rooted = False\<rparr>)]
                        ,edges = Mapping [(1, \<lparr>edge_src = 1, edge_trg = 2, edge_mark = RuleMarkEdge_None, edge_label = [Var 2]\<rparr>)]\<rparr>
            ,rule_interf = {1,2}\<rparr>"

definition col_blue_2 :: ruleschema where
"col_blue_2 = \<lparr>rule_ty = Mapping [(0, Lty), (1, Lty), (2, Lty)]
            ,rule_lhs = \<lparr>nodes = Mapping
                                 [(1, \<lparr>node_mark = RuleMarkNode_Red , node_label = [Var 0], node_rooted = False\<rparr>)
                                 ,(2, \<lparr>node_mark = RuleMarkNode_None, node_label = [Var 1], node_rooted = False\<rparr>)]
                        ,edges = Mapping [(1, \<lparr>edge_src = 2, edge_trg = 1, edge_mark = RuleMarkEdge_None, edge_label = [Var 2]\<rparr>)]\<rparr>
            ,rule_rhs = \<lparr>nodes = Mapping
                                 [(1, \<lparr>node_mark = RuleMarkNode_Red , node_label = [Var 0], node_rooted = False\<rparr>)
                                 ,(2, \<lparr>node_mark = RuleMarkNode_Blue, node_label = [Var 1], node_rooted = False\<rparr>)]
                        ,edges = Mapping [(1, \<lparr>edge_src = 2, edge_trg = 1, edge_mark = RuleMarkEdge_None, edge_label = [Var 2]\<rparr>)]\<rparr>
            ,rule_interf = {1,2}\<rparr>"
             
definition col_red_1 :: ruleschema where
"col_red_1 = \<lparr>rule_ty = Mapping [(0, Lty), (1, Lty), (2, Lty)]
           ,rule_lhs = \<lparr>nodes = Mapping
                                [(1, \<lparr>node_mark = RuleMarkNode_Blue , node_label = [Var 0], node_rooted = False\<rparr>)
                                ,(2, \<lparr>node_mark = RuleMarkNode_None, node_label = [Var 1], node_rooted = False\<rparr>)]
                       ,edges = Mapping [(1, \<lparr>edge_src = 1, edge_trg = 2, edge_mark = RuleMarkEdge_None, edge_label = [Var 2]\<rparr>)]\<rparr>
           ,rule_rhs = \<lparr>nodes = Mapping 
                                [(1, \<lparr>node_mark = RuleMarkNode_Blue , node_label = [Var 0], node_rooted = False\<rparr>)
                                ,(2, \<lparr>node_mark = RuleMarkNode_Red, node_label = [Var 1], node_rooted = False\<rparr>)]
                       ,edges = Mapping [(1, \<lparr>edge_src = 1, edge_trg = 2, edge_mark = RuleMarkEdge_None, edge_label = [Var 2]\<rparr>)]\<rparr>
           ,rule_interf = {1,2}\<rparr>"

             
definition col_red_2 :: ruleschema where
"col_red_2 = \<lparr>rule_ty = Mapping [(0, Lty), (1, Lty), (2, Lty)]
           ,rule_lhs = \<lparr>nodes = Mapping
                                [(1, \<lparr>node_mark = RuleMarkNode_Blue , node_label = [Var 0], node_rooted = False\<rparr>)
                                ,(2, \<lparr>node_mark = RuleMarkNode_None, node_label = [Var 1], node_rooted = False\<rparr>)]
                       ,edges = Mapping [(1, \<lparr>edge_src = 2, edge_trg = 1, edge_mark = RuleMarkEdge_None, edge_label = [Var 2]\<rparr>)]\<rparr>
           ,rule_rhs = \<lparr>nodes = Mapping 
                                [(1, \<lparr>node_mark = RuleMarkNode_Blue , node_label = [Var 0], node_rooted = False\<rparr>)
                                ,(2, \<lparr>node_mark = RuleMarkNode_Red, node_label = [Var 1], node_rooted = False\<rparr>)]
                       ,edges = Mapping [(1, \<lparr>edge_src = 2, edge_trg = 1, edge_mark = RuleMarkEdge_None, edge_label = [Var 2]\<rparr>)]\<rparr>
           ,rule_interf = {1,2}\<rparr>"

definition ill_blue :: ruleschema where
"ill_blue = \<lparr>rule_ty = Mapping [(0, Lty), (1, Lty), (2, Lty)]
            ,rule_lhs = \<lparr>nodes = Mapping
                                 [(1, \<lparr>node_mark = RuleMarkNode_Blue, node_label = [Var 0], node_rooted = False\<rparr>)
                                 ,(2, \<lparr>node_mark = RuleMarkNode_Blue, node_label = [Var 1], node_rooted = False\<rparr>)]
                        ,edges = Mapping [(1, \<lparr>edge_src = 1, edge_trg = 2, edge_mark = RuleMarkEdge_None, edge_label = [Var 2]\<rparr>)]\<rparr>
            ,rule_rhs = \<lparr>nodes = Mapping
                                 [(1, \<lparr>node_mark = RuleMarkNode_Blue, node_label = [Var 0], node_rooted = False\<rparr>)
                                 ,(2, \<lparr>node_mark = RuleMarkNode_Blue, node_label = [Var 1], node_rooted = False\<rparr>)]
                        ,edges = Mapping [(1, \<lparr>edge_src = 1, edge_trg = 2, edge_mark = RuleMarkEdge_None, edge_label = [Var 2]\<rparr>)]\<rparr>
            ,rule_interf = {1,2}\<rparr>"

definition ill_red :: ruleschema where
"ill_red = \<lparr>rule_ty = Mapping [(0, Lty), (1, Lty), (2, Lty)]
           ,rule_lhs = \<lparr>nodes = Mapping
                                [(1, \<lparr>node_mark = RuleMarkNode_Red, node_label = [Var 0], node_rooted = False\<rparr>)
                                ,(2, \<lparr>node_mark = RuleMarkNode_Red, node_label = [Var 1], node_rooted = False\<rparr>)]
                       ,edges = Mapping [(1, \<lparr>edge_src = 1, edge_trg = 2, edge_mark = RuleMarkEdge_None, edge_label = [Var 2]\<rparr>)]\<rparr>
           ,rule_rhs = \<lparr>nodes = Mapping
                                [(1, \<lparr>node_mark = RuleMarkNode_Red, node_label = [Var 0], node_rooted = False\<rparr>)
                                ,(2, \<lparr>node_mark = RuleMarkNode_Red, node_label = [Var 1], node_rooted = False\<rparr>)]
                       ,edges = Mapping [(1, \<lparr>edge_src = 1, edge_trg = 2, edge_mark = RuleMarkEdge_None, edge_label = [Var 2]\<rparr>)]\<rparr>
           ,rule_interf = {1,2}\<rparr>"

lemma "wf_ruleschema ill_red"
  by (simp add: ill_red_def)

lemma "wf_ruleschema ill_blue"
  by (simp add: ill_blue_def)

lemma "wf_ruleschema col_red"
  by (simp add: col_red_def)

lemma "wf_ruleschema col_blue"
  by (simp add: col_blue_def)

definition twocolouring :: com where
"twocolouring \<equiv> (RuleApp init ;; RuleSet {col_blue :: rule, col_red:: rule}!)! ;; 
  IF RuleSet {ill_blue :: rule, ill_red :: rule} THEN RuleApp unmark! ELSE Skip"


abbreviation c :: "form" where
"c == (\<lceil>\<forall> 0 : Node\<rceil> \<lceil>mark \<langle>0\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_None \<lceil>\<and>\<rceil> \<lceil>unrooted \<langle>0\<rangle>\<rceil>) \<lceil>\<and>\<rceil>
      (\<lceil>\<forall> 0 : Edge\<rceil> \<lceil>mark \<langle>0\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>E RuleMarkEdge_None)"


abbreviation d :: form where
"d == (\<lceil>\<forall> 0 : Node\<rceil> \<lceil>mark \<langle>0\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Red  \<lceil>\<or>\<rceil>\<lceil>mark \<langle>0\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Blue) \<lceil>\<and>\<rceil>
      \<lceil>\<not>\<rceil>(\<lceil>\<exists> 0 : Edge\<rceil> (\<lceil>src \<langle>0\<rangle>\<rceil> \<lceil>\<noteq>\<rceil> \<lceil>trg \<langle>0\<rangle>\<rceil>) \<lceil>\<and>\<rceil>
                     \<lceil>mark \<lceil>src \<langle>0\<rangle>\<rceil>\<rceil> \<lceil>=\<rceil> \<lceil>mark \<lceil>trg \<langle>0\<rangle>\<rceil>\<rceil>)"

abbreviation e :: form where
"e == (\<lceil>\<forall> 0 : Node\<rceil> (\<lceil>mark \<langle>0\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Red \<lceil>\<or>\<rceil> \<lceil>mark \<langle>0\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Blue) \<lceil>\<and>\<rceil> \<lceil>unrooted \<langle>0\<rangle>\<rceil>) \<lceil>\<and>\<rceil>
      (\<lceil>\<forall> 0 : Edge\<rceil>  \<lceil>mark \<langle>0\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>E RuleMarkEdge_None)"

abbreviation f :: form where
"f == (\<lceil>\<forall> 0 : Node\<rceil> (\<lceil>mark \<langle>0\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Red \<lceil>\<or>\<rceil> \<lceil>mark \<langle>0\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Blue \<lceil>\<or>\<rceil> 
        \<lceil>mark \<langle>0\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_None) \<lceil>\<and>\<rceil> \<lceil>unrooted \<langle>0\<rangle>\<rceil>) \<lceil>\<and>\<rceil>
      (\<lceil>\<forall> 0 : Edge\<rceil>  \<lceil>mark \<langle>0\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>E RuleMarkEdge_None)"


section \<open>SLP proofs\<close>

lemma "eval g undefined (Slp f (init:: rule)  \<lceil>\<longleftrightarrow>\<rceil> 
  ((\<lceil>\<exists>0: Node\<rceil> (\<lceil>\<forall>1: Node\<rceil> (\<langle>1\<rangle> \<lceil>=\<rceil> \<langle>0\<rangle> 
    \<lceil>\<or>\<rceil> ((\<lceil>mark \<langle>1\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Red \<lceil>\<or>\<rceil> \<lceil>mark \<langle>1\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Blue \<lceil>\<or>\<rceil> \<lceil>mark \<langle>1\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_None)\<lceil>\<and>\<rceil> \<lceil>unrooted \<langle>1\<rangle>\<rceil>)) 
  \<lceil>\<and>\<rceil> \<lceil>mark \<langle>0\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Red \<lceil>\<and>\<rceil> \<lceil>unrooted \<langle>0\<rangle>\<rceil>)) \<lceil>\<and>\<rceil> (\<lceil>\<forall>1: Edge\<rceil> (\<lceil>mark \<langle>1\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>E RuleMarkEdge_None))))"
  apply code_simp
  by auto


value "Slp f (col_blue_1::rule)"
value "Slp f (col_blue_2::rule)"
value "Slp f (col_red_1::rule)" 
(* 
lemma "eval g undefined ((Slp f (col_blue_1:: rule) \<lceil>\<or>\<rceil> Slp f (col_blue_2:: rule)) \<lceil>\<longleftrightarrow>\<rceil> 
  (Slp f (col_red_1:: rule) \<lceil>\<or>\<rceil>  Slp f (col_red_2:: rule)))"
  apply code_simp
  apply auto
     apply (smt (z3))
  apply (smt (z3))
   apply (smt (z3))
  by (smt (z3)) *)



(* 

lemma "eval g undefined (Slp f (col_blue:: rule) \<lceil>\<longleftrightarrow>\<rceil> Slp f (col_red:: rule))"
   apply code_simp
   apply auto
  oops
  


  oops

lemma "eval g undefined (((\<lceil>\<exists>0: Node\<rceil> (\<lceil>\<exists>1: Node\<rceil> ((\<lceil>\<forall>2: Node\<rceil> (\<langle>2\<rangle> \<lceil>=\<rceil> \<langle>0\<rangle> \<lceil>\<or>\<rceil> \<langle>2\<rangle> \<lceil>=\<rceil> \<langle>1\<rangle> \<lceil>\<or>\<rceil>
    ((\<lceil>mark \<langle>2\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Red \<lceil>\<or>\<rceil> \<lceil>mark \<langle>2\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Blue \<lceil>\<or>\<rceil> \<lceil>mark \<langle>2\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_None) \<lceil>\<and>\<rceil> \<lceil>unrooted \<langle>2\<rangle>\<rceil>)))
  \<lceil>\<and>\<rceil> \<lceil>mark \<langle>0\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Red \<lceil>\<and>\<rceil> \<lceil>mark \<langle>1\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Blue \<lceil>\<and>\<rceil> \<lceil>unrooted \<langle>0\<rangle>\<rceil> \<lceil>\<and>\<rceil> \<lceil>unrooted \<langle>1\<rangle>\<rceil>
  \<lceil>\<and>\<rceil> (\<lceil>\<exists>3: Edge\<rceil> ((\<lceil>src \<langle>3\<rangle>\<rceil> \<lceil>=\<rceil> \<langle>0\<rangle> \<lceil>\<and>\<rceil> \<lceil>trg \<langle>3\<rangle>\<rceil> \<lceil>=\<rceil> \<langle>1\<rangle>) \<lceil>\<or>\<rceil> (\<lceil>src \<langle>3\<rangle>\<rceil> \<lceil>=\<rceil> \<langle>1\<rangle> \<lceil>\<and>\<rceil> \<lceil>trg \<langle>3\<rangle>\<rceil> \<lceil>=\<rceil> \<langle>0\<rangle>)) )))) \<lceil>\<and>\<rceil> (\<lceil>\<forall>4:Edge\<rceil> (\<lceil>mark \<langle>4\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>E RuleMarkEdge_None)))  \<lceil>\<longrightarrow>\<rceil>  Slp f (col_blue:: rule))"
  apply code_simp
  apply auto
   apply (erule notE)
   apply (smt (z3) conv_mark_node.elims mark_eq_node.simps(12) mark_eq_node.simps(15) mark_eq_node.simps(23) mark_eq_node.simps(24) mark_eq_node.simps(26) rulemark_node.distinct(13))
  apply (erule notE)
  apply (rule spec)
  oops  


  text \<open>
    Slp f col_blue implies rule
  \<close>
*)
lemma x[simp]:"mark_eq_node (conv_mark_node HostMarkNode_Red) RuleMarkNode_Red"
  by simp


lemma xxx: "\<And>e. \<forall>e\<in>Mapping.keys (edges g).
            (\<exists>y. Mapping.lookup (nodes g) (edge_trg (the (Mapping.lookup (edges g) e))) = Some y) \<and>
            (\<exists>y. Mapping.lookup (nodes g) (edge_src (the (Mapping.lookup (edges g) e))) = Some y) \<Longrightarrow>
         edge_src (the (Mapping.lookup (edges g) e)) \<in> Mapping.keys (nodes g) \<Longrightarrow>
         edge_trg (the (Mapping.lookup (edges g) e)) \<in> Mapping.keys (nodes g) \<Longrightarrow>
         \<forall>e\<in>Mapping.keys (edges g). mark_eq_edge (conv_mark_edge (edge_mark (the (Mapping.lookup (edges g) e)))) RuleMarkEdge_None \<Longrightarrow>
         \<forall>n\<in>Mapping.keys (nodes g).
            mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) n)))) RuleMarkNode_Blue \<longrightarrow>
            (\<forall>na\<in>Mapping.keys (nodes g).
                mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) na)))) RuleMarkNode_Red \<longrightarrow>
                n = na \<or>
                na = n \<or>
                (\<exists>nb\<in>Mapping.keys (nodes g).
                    nb \<noteq> na \<and>
                    nb \<noteq> n \<and>
                    (\<not> mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) nb)))) RuleMarkNode_Red \<and>
                     \<not> mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) nb)))) RuleMarkNode_Blue \<and>
                     \<not> mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) nb)))) RuleMarkNode_None \<or>
                     node_rooted (the (Mapping.lookup (nodes g) nb)))) \<or>
                node_rooted (the (Mapping.lookup (nodes g) na)) \<or>
                node_rooted (the (Mapping.lookup (nodes g) n)) \<or>
                (\<forall>e\<in>Mapping.keys (edges g). edge_src (the (Mapping.lookup (edges g) e)) = n \<longrightarrow> edge_trg (the (Mapping.lookup (edges g) e)) \<noteq> na)) \<Longrightarrow>
         \<forall>n\<in>Mapping.keys (nodes g).
            \<forall>na\<in>Mapping.keys (nodes g).
               mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) na)))) RuleMarkNode_Blue \<longrightarrow>
               mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) n)))) RuleMarkNode_Red \<longrightarrow>
               n = na \<or>
               na = n \<or>
               (\<exists>nb\<in>Mapping.keys (nodes g).
                   nb \<noteq> n \<and>
                   nb \<noteq> na \<and>
                   (\<not> mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) nb)))) RuleMarkNode_Red \<and>
                    \<not> mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) nb)))) RuleMarkNode_Blue \<and>
                    \<not> mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) nb)))) RuleMarkNode_None \<or>
                    node_rooted (the (Mapping.lookup (nodes g) nb)))) \<or>
               node_rooted (the (Mapping.lookup (nodes g) n)) \<or>
               node_rooted (the (Mapping.lookup (nodes g) na)) \<or>
               (\<forall>e\<in>Mapping.keys (edges g). edge_src (the (Mapping.lookup (edges g) e)) = n \<longrightarrow> edge_trg (the (Mapping.lookup (edges g) e)) \<noteq> na) \<Longrightarrow>
         mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) (edge_trg (the (Mapping.lookup (edges g) e))))))) RuleMarkNode_Blue \<Longrightarrow>
         mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) (edge_src (the (Mapping.lookup (edges g) e))))))) RuleMarkNode_Red \<Longrightarrow>
         \<forall>n\<in>Mapping.keys (nodes g).
            n = edge_src (the (Mapping.lookup (edges g) e)) \<or>
            n = edge_trg (the (Mapping.lookup (edges g) e)) \<or>
            (mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) n)))) RuleMarkNode_Red \<or>
             mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) n)))) RuleMarkNode_Blue \<or>
             mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) n)))) RuleMarkNode_None) \<and>
            \<not> node_rooted (the (Mapping.lookup (nodes g) n)) \<Longrightarrow>
         \<not> node_rooted (the (Mapping.lookup (nodes g) (edge_src (the (Mapping.lookup (edges g) e))))) \<Longrightarrow>
         \<not> node_rooted (the (Mapping.lookup (nodes g) (edge_trg (the (Mapping.lookup (edges g) e))))) \<Longrightarrow> e \<in> Mapping.keys (edges g) \<Longrightarrow> False"
proof -
  fix e :: nat
  assume a1: "mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) (edge_trg (the (Mapping.lookup (edges g) e))))))) RuleMarkNode_Blue"
  assume a2: "mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) (edge_src (the (Mapping.lookup (edges g) e))))))) RuleMarkNode_Red"
  assume a3: "edge_trg (the (Mapping.lookup (edges g) e)) \<in> Mapping.keys (nodes g)"
  assume a4: "\<not> node_rooted (the (Mapping.lookup (nodes g) (edge_src (the (Mapping.lookup (edges g) e)))))"
  assume a5: "\<not> node_rooted (the (Mapping.lookup (nodes g) (edge_trg (the (Mapping.lookup (edges g) e)))))"
  assume a6: "edge_src (the (Mapping.lookup (edges g) e)) \<in> Mapping.keys (nodes g)"
  assume a7: "\<forall>n\<in>Mapping.keys (nodes g). \<forall>na\<in>Mapping.keys (nodes g). mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) na)))) RuleMarkNode_Blue \<longrightarrow> mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) n)))) RuleMarkNode_Red \<longrightarrow> n = na \<or> na = n \<or> (\<exists>nb\<in>Mapping.keys (nodes g). nb \<noteq> n \<and> nb \<noteq> na \<and> (\<not> mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) nb)))) RuleMarkNode_Red \<and> \<not> mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) nb)))) RuleMarkNode_Blue \<and> \<not> mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) nb)))) RuleMarkNode_None \<or> node_rooted (the (Mapping.lookup (nodes g) nb)))) \<or> node_rooted (the (Mapping.lookup (nodes g) n)) \<or> node_rooted (the (Mapping.lookup (nodes g) na)) \<or> (\<forall>e\<in>Mapping.keys (edges g). edge_src (the (Mapping.lookup (edges g) e)) = n \<longrightarrow> edge_trg (the (Mapping.lookup (edges g) e)) \<noteq> na)"
  assume a8: "\<forall>n\<in>Mapping.keys (nodes g). n = edge_src (the (Mapping.lookup (edges g) e)) \<or> n = edge_trg (the (Mapping.lookup (edges g) e)) \<or> (mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) n)))) RuleMarkNode_Red \<or> mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) n)))) RuleMarkNode_Blue \<or> mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) n)))) RuleMarkNode_None) \<and> \<not> node_rooted (the (Mapping.lookup (nodes g) n))"
  assume a9: "e \<in> Mapping.keys (edges g)"
  obtain nn :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"\<forall>x0 x1. (\<exists>v2. v2 \<in> Mapping.keys (nodes g) \<and> v2 \<noteq> x1 \<and> v2 \<noteq> x0 \<and> (\<not> mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) v2)))) RuleMarkNode_Red \<and> \<not> mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) v2)))) RuleMarkNode_Blue \<and> \<not> mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) v2)))) RuleMarkNode_None \<or> node_rooted (the (Mapping.lookup (nodes g) v2)))) = (nn x0 x1 \<in> Mapping.keys (nodes g) \<and> nn x0 x1 \<noteq> x1 \<and> nn x0 x1 \<noteq> x0 \<and> (\<not> mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) (nn x0 x1))))) RuleMarkNode_Red \<and> \<not> mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) (nn x0 x1))))) RuleMarkNode_Blue \<and> \<not> mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) (nn x0 x1))))) RuleMarkNode_None \<or> node_rooted (the (Mapping.lookup (nodes g) (nn x0 x1)))))"
    by moura
  then have f10: "\<forall>n. n \<notin> Mapping.keys (nodes g) \<or> (\<forall>na. (na \<notin> Mapping.keys (nodes g) \<or> \<not> mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) na)))) RuleMarkNode_Blue \<or> \<not> mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) n)))) RuleMarkNode_Red) \<or> n = na \<or> na = n \<or> nn na n \<in> Mapping.keys (nodes g) \<and> nn na n \<noteq> n \<and> nn na n \<noteq> na \<and> (\<not> mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) (nn na n))))) RuleMarkNode_Red \<and> \<not> mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) (nn na n))))) RuleMarkNode_Blue \<and> \<not> mark_eq_node (conv_mark_node (node_mark (the (Mapping.lookup (nodes g) (nn na n))))) RuleMarkNode_None \<or> node_rooted (the (Mapping.lookup (nodes g) (nn na n)))) \<or> node_rooted (the (Mapping.lookup (nodes g) n)) \<or> node_rooted (the (Mapping.lookup (nodes g) na)) \<or> (\<forall>nb. (nb \<notin> Mapping.keys (edges g) \<or> edge_src (the (Mapping.lookup (edges g) nb)) \<noteq> n) \<or> edge_trg (the (Mapping.lookup (edges g) nb)) \<noteq> na))"
    using a7 by (simp add: Ball_def_raw Bex_def_raw)
  have "conv_mark_node (node_mark (the (Mapping.lookup (nodes g) (edge_trg (the (Mapping.lookup (edges g) e)))))) \<noteq> RuleMarkNode_Green"
    using a1 by force
  then show False
    using f10 a9 a8 a6 a5 a4 a3 a2 a1 by (smt (z3) conv_mark_node.elims mark_eq_node.simps(12) mark_eq_node.simps(15) mark_eq_node.simps(16) mark_eq_node.simps(23) rulemark_node.distinct(13))
qed

lemma "\<lbrakk>wf_ruleschema col_blue_1; wf_ruleschema col_blue_2; wf_graph g\<rbrakk> 
  \<Longrightarrow> eval g undefined ((Slp f (col_blue_1:: rule) \<lceil>\<or>\<rceil> Slp f (col_blue_2:: rule))  \<lceil>\<longleftrightarrow>\<rceil>   
  (\<lceil>\<exists>0: Node\<rceil> (\<lceil>\<exists>1: Node\<rceil> ((\<lceil>\<forall>2: Node\<rceil> (\<langle>2\<rangle> \<lceil>=\<rceil> \<langle>0\<rangle> \<lceil>\<or>\<rceil> \<langle>2\<rangle> \<lceil>=\<rceil> \<langle>1\<rangle> \<lceil>\<or>\<rceil>
    ((\<lceil>mark \<langle>2\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Red \<lceil>\<or>\<rceil> \<lceil>mark \<langle>2\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Blue \<lceil>\<or>\<rceil> \<lceil>mark \<langle>2\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_None) \<lceil>\<and>\<rceil> \<lceil>unrooted \<langle>2\<rangle>\<rceil>)))
  \<lceil>\<and>\<rceil> \<lceil>mark \<langle>0\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Red \<lceil>\<and>\<rceil> \<lceil>mark \<langle>1\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Blue \<lceil>\<and>\<rceil> \<lceil>unrooted \<langle>0\<rangle>\<rceil> \<lceil>\<and>\<rceil> \<lceil>unrooted \<langle>1\<rangle>\<rceil>
  \<lceil>\<and>\<rceil> (\<lceil>\<exists>3: Edge\<rceil> ((\<lceil>src \<langle>3\<rangle>\<rceil> \<lceil>=\<rceil> \<langle>0\<rangle> \<lceil>\<and>\<rceil> \<lceil>trg \<langle>3\<rangle>\<rceil> \<lceil>=\<rceil> \<langle>1\<rangle>) \<lceil>\<or>\<rceil> (\<lceil>src \<langle>3\<rangle>\<rceil> \<lceil>=\<rceil> \<langle>1\<rangle> \<lceil>\<and>\<rceil> \<lceil>trg \<langle>3\<rangle>\<rceil> \<lceil>=\<rceil> \<langle>0\<rangle>)) )))) \<lceil>\<and>\<rceil> (\<lceil>\<forall>4:Edge\<rceil> (\<lceil>mark \<langle>4\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>E RuleMarkEdge_None)))"
  apply code_simp
  apply safe
  apply auto
     apply (metis (no_types, lifting))
    apply (metis (no_types, hide_lams))
   apply (rule xxx)
              apply blast+
  apply (rule xxx)
             apply blast+
  by (metis (no_types, hide_lams))+



  
  
  
(*
lemma "eval g undefined (Slp f (col_red:: rule)  \<lceil>\<longrightarrow>\<rceil>  
  (\<lceil>\<exists>0: Node\<rceil> (\<lceil>\<exists>1: Node\<rceil> ((\<lceil>\<forall>2: Node\<rceil> (\<langle>2\<rangle> \<lceil>=\<rceil> \<langle>0\<rangle> \<lceil>\<or>\<rceil> \<langle>2\<rangle> \<lceil>=\<rceil> \<langle>1\<rangle> \<lceil>\<or>\<rceil>
    ((\<lceil>mark \<langle>2\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Red \<lceil>\<or>\<rceil> \<lceil>mark \<langle>2\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Blue \<lceil>\<or>\<rceil> \<lceil>mark \<langle>2\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_None) \<lceil>\<and>\<rceil> \<lceil>unrooted \<langle>2\<rangle>\<rceil>)))
  \<lceil>\<and>\<rceil> \<lceil>mark \<langle>0\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Red \<lceil>\<and>\<rceil> \<lceil>mark \<langle>1\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Blue \<lceil>\<and>\<rceil> \<lceil>unrooted \<langle>0\<rangle>\<rceil> \<lceil>\<and>\<rceil> \<lceil>unrooted \<langle>1\<rangle>\<rceil>
  \<lceil>\<and>\<rceil> (\<lceil>\<exists>3: Edge\<rceil> ((\<lceil>src \<langle>3\<rangle>\<rceil> \<lceil>=\<rceil> \<langle>0\<rangle> \<lceil>\<and>\<rceil> \<lceil>trg \<langle>3\<rangle>\<rceil> \<lceil>=\<rceil> \<langle>1\<rangle>) \<lceil>\<or>\<rceil> (\<lceil>src \<langle>3\<rangle>\<rceil> \<lceil>=\<rceil> \<langle>1\<rangle> \<lceil>\<and>\<rceil> \<lceil>trg \<langle>3\<rangle>\<rceil> \<lceil>=\<rceil> \<langle>0\<rangle>)) )))) \<lceil>\<and>\<rceil> (\<lceil>\<forall>4:Edge\<rceil> (\<lceil>mark \<langle>4\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>E RuleMarkEdge_None)))"
  apply code_simp
  by auto  

lemma "eval g undefined (Slp f (col_red:: rule)  \<lceil>\<longleftrightarrow>\<rceil>
  ((\<lceil>\<exists>0: Node\<rceil> 
    (\<lceil>\<exists>1: Node\<rceil> 
      ((\<lceil>\<forall>2: Node\<rceil> (\<langle>2\<rangle> \<lceil>=\<rceil> \<langle>0\<rangle> \<lceil>\<or>\<rceil> \<langle>2\<rangle> \<lceil>=\<rceil> \<langle>1\<rangle> \<lceil>\<or>\<rceil>
        ((\<lceil>mark \<langle>2\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Red \<lceil>\<or>\<rceil> \<lceil>mark \<langle>2\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Blue \<lceil>\<or>\<rceil> \<lceil>mark \<langle>2\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_None) \<lceil>\<and>\<rceil> \<lceil>unrooted \<langle>2\<rangle>\<rceil>) ))
  \<lceil>\<and>\<rceil> \<lceil>mark \<langle>0\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Red \<lceil>\<and>\<rceil> \<lceil>mark \<langle>1\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Blue \<lceil>\<and>\<rceil> \<lceil>unrooted \<langle>0\<rangle>\<rceil> \<lceil>\<and>\<rceil> \<lceil>unrooted \<langle>1\<rangle>\<rceil>
  \<lceil>\<and>\<rceil> (\<lceil>\<exists>3: Edge\<rceil> ((\<lceil>src \<langle>3\<rangle>\<rceil> \<lceil>=\<rceil> \<langle>0\<rangle> \<lceil>\<and>\<rceil> \<lceil>trg \<langle>3\<rangle>\<rceil> \<lceil>=\<rceil> \<langle>1\<rangle>) \<lceil>\<or>\<rceil> (\<lceil>src \<langle>3\<rangle>\<rceil> \<lceil>=\<rceil> \<langle>1\<rangle> \<lceil>\<and>\<rceil> \<lceil>trg \<langle>3\<rangle>\<rceil> \<lceil>=\<rceil> \<langle>0\<rangle>)) )))) \<lceil>\<and>\<rceil> (\<lceil>\<forall>4:Edge\<rceil> (\<lceil>mark \<langle>4\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>E RuleMarkEdge_None))))"
  apply code_simp
  apply auto
  oops
 *)
  
  
lemma "eval g undefined (Slp f (unmark :: rule)  \<lceil>\<longleftrightarrow>\<rceil>  
  (\<lceil>\<exists>1: Node\<rceil> ((\<lceil>\<forall>0: Node\<rceil> (\<langle>0\<rangle> \<lceil>=\<rceil> \<langle>1\<rangle> \<lceil>\<or>\<rceil> 
    ((\<lceil>mark \<langle>0\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Red \<lceil>\<or>\<rceil> \<lceil>mark \<langle>0\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Blue \<lceil>\<or>\<rceil> \<lceil>mark \<langle>0\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_None) \<lceil>\<and>\<rceil> \<lceil>unrooted \<langle>0\<rangle>\<rceil>)))
  \<lceil>\<and>\<rceil> \<lceil>mark \<langle>1\<rangle>\<rceil> \<lceil>=\<rceil>\<triangleright>\<^sub>V RuleMarkNode_None \<lceil>\<and>\<rceil> \<lceil>unrooted \<langle>1\<rangle>\<rceil>)) \<lceil>\<and>\<rceil> (\<lceil>\<forall>4:Edge\<rceil> (\<lceil>mark \<langle>4\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>E RuleMarkEdge_None)))"
  apply code_simp
  by auto





lemma c_impl_f : "eval g undefined (c \<lceil>\<longrightarrow>\<rceil> f)" 
  by clarsimp

(* section \<open>Proof of Fail output\<close> *)
(* 
lemma "eval g undefined (Fail (RuleSet {col_blue::rule, col_red::rule}) \<lceil>\<longleftrightarrow>\<rceil> 
  (\<lceil>\<not>\<rceil>(\<lceil>\<exists> x: Edge\<rceil> ((((\<lceil>mark \<lceil>src \<langle>x\<rangle>\<rceil>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Red \<lceil>\<or>\<rceil> \<lceil>mark \<lceil>src \<langle>x\<rangle>\<rceil>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Blue) \<lceil>\<and>\<rceil> \<lceil>mark \<lceil>src \<langle>x\<rangle>\<rceil>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_None) \<lceil>\<or>\<rceil>
                     ((\<lceil>mark \<lceil>trg \<langle>x\<rangle>\<rceil>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Red \<lceil>\<or>\<rceil> \<lceil>mark \<lceil>trg \<langle>x\<rangle>\<rceil>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Blue) \<lceil>\<and>\<rceil> \<lceil>mark \<lceil>src \<langle>x\<rangle>\<rceil>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_None) ) \<lceil>\<and>\<rceil>
  \<lceil>unrooted \<lceil>src \<langle>x\<rangle>\<rceil>\<rceil> \<lceil>\<and>\<rceil> \<lceil>unrooted \<lceil>trg \<langle>x\<rangle>\<rceil>\<rceil>) )))"
  apply auto
  oops

lemma "eval g undefined (Fail (RuleApp init ;; RuleSet {col_blue::rule, col_red::rule}!) \<lceil>\<longleftrightarrow>\<rceil> 
  (\<lceil>\<not>\<rceil>(\<lceil>\<exists> x : Node\<rceil> (\<lceil>mark \<langle>x\<rangle>\<rceil> \<lceil>=\<rceil>  \<triangleright>\<^sub>V RuleMarkNode_None \<lceil>\<and>\<rceil> \<lceil>unrooted \<langle>x\<rangle>\<rceil>))))"
  apply auto
  sorry


lemma "eval g undefined (Fail (RuleApp unmark) \<lceil>\<longleftrightarrow>\<rceil> (\<lceil>\<not>\<rceil>(\<lceil>\<exists>x:Node\<rceil> (\<lceil>mark \<langle>x\<rangle>\<rceil> \<lceil>\<noteq>\<rceil> \<triangleright>\<^sub>V RuleMarkNode_None \<lceil>\<and>\<rceil> \<lceil>unrooted \<langle>x\<rangle>\<rceil>))))"
  apply (simp add: unmark_def)
  apply (rule conjI)
   apply (rule disjI1)
   apply (simp add: set_to_list_def)
   apply (rule someI2_ex)
  apply (metis empty_set list.simps(15))
  apply (induct g rule: eval.induct)


lemma "\<turnstile> {c} twocolouring {c \<lceil>\<or>\<rceil> d}"
  apply (simp add: twocolouring_def)
  apply (rule Cons [where ?c' = f and ?d' = "c \<lceil>\<or>\<rceil> d"])
    apply auto
  apply (rule Comp [where ?e = e])
\<comment> \<open>subtree I\<close>
   apply (rule Cons [where ?c' = f and d'="f \<lceil>\<and>\<rceil> Fail (RuleApp init ;; RuleSet {col_blue::rule, col_red::rule}!)"])
     apply auto
    prefer 2
  oops
 *)

(*     prefer 2
    using c_impl_f apply blast
     prefer 2
    apply auto
  apply (rule Comp [where ?e = e])
     apply (rule Cons [where ?c' = f and ?d' = "f \<lceil>\<and>\<rceil> Fail (RuleApp init ;; RuleSet {col_blue::rule, col_red::rule}!)"])
       prefer 2
       apply auto
      prefer 2
    apply (simp add: dom_def)
    oops

 *)end