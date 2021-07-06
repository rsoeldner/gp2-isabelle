theory TwoColouringEx
  imports Rule FOLoG
begin

abbreviation cast_ruleschema_rule :: "ruleschema \<Rightarrow> rule" where
"cast_ruleschema_rule rs \<equiv> (rs, cond.T)"

declare [[coercion_enabled]]
declare [[coercion cast_ruleschema_rule]]



definition init :: ruleschema where
"init = \<lparr>rule_ty = [''a'' \<mapsto> Lty],
         rule_lhs = \<lparr>nodes = [1 \<mapsto> \<lparr>node_mark = RuleMarkNode_None, node_label= Var ''a'' # [], node_rooted=False\<rparr>]
                   ,edges = Map.empty\<rparr>,
         rule_rhs = \<lparr>nodes = [1 \<mapsto> \<lparr>node_mark = RuleMarkNode_Red, node_label= Var ''a'' # [] , node_rooted=False\<rparr>]
               ,edges = Map.empty\<rparr>,
         rule_interf = {1}\<rparr>"

definition unmark :: rule where
"unmark = (\<lparr>rule_ty = [''a'' \<mapsto> Lty],
           rule_lhs = \<lparr>nodes = [1 \<mapsto> \<lparr>node_mark = RuleMarkNode_Any, node_label= Var ''a'' # [] , node_rooted=False\<rparr>]
                 ,edges = Map.empty\<rparr>,
           rule_rhs = \<lparr>nodes = [1 \<mapsto> \<lparr>node_mark = RuleMarkNode_None, node_label= Var ''a'' # [], node_rooted=False\<rparr>]
                 ,edges = Map.empty\<rparr>,
           rule_interf = {1}\<rparr>, cond.T)"

definition col_blue :: ruleschema where
"col_blue = \<lparr>rule_ty = [''a'' \<mapsto> Lty, ''b'' \<mapsto> Lty, ''c'' \<mapsto> Lty]
            ,rule_lhs = \<lparr>nodes = [1 \<mapsto> \<lparr>node_mark = RuleMarkNode_Red , node_label = [Var ''a''], node_rooted = False\<rparr>
                                 ,1 \<mapsto> \<lparr>node_mark = RuleMarkNode_None, node_label = [Var ''b''], node_rooted = False\<rparr>]
                        ,edges = [1 \<mapsto> \<lparr>edge_src = 1, edge_trg = 2, edge_mark = RuleMarkEdge_None, edge_label = [Var ''c'']\<rparr>]\<rparr>
            ,rule_rhs = \<lparr>nodes = [1 \<mapsto> \<lparr>node_mark = RuleMarkNode_Red , node_label = [Var ''a''], node_rooted = False\<rparr>
                                 ,1 \<mapsto> \<lparr>node_mark = RuleMarkNode_Blue, node_label = [Var ''b''], node_rooted = False\<rparr>]
                        ,edges = [1 \<mapsto> \<lparr>edge_src = 1, edge_trg = 2, edge_mark = RuleMarkEdge_None, edge_label = [Var ''c'']\<rparr>]\<rparr>
            ,rule_interf = {1,2}\<rparr>"
             
definition col_red :: ruleschema where
"col_red = \<lparr>rule_ty = [''a'' \<mapsto> Lty, ''b'' \<mapsto> Lty, ''c'' \<mapsto> Lty]
           ,rule_lhs = \<lparr>nodes = [1 \<mapsto> \<lparr>node_mark = RuleMarkNode_Blue , node_label = [Var ''a''], node_rooted = False\<rparr>
                                ,1 \<mapsto> \<lparr>node_mark = RuleMarkNode_None, node_label = [Var ''b''], node_rooted = False\<rparr>]
                       ,edges = [1 \<mapsto> \<lparr>edge_src = 1, edge_trg = 2, edge_mark = RuleMarkEdge_None, edge_label = [Var ''c'']\<rparr>]\<rparr>
           ,rule_rhs = \<lparr>nodes = [1 \<mapsto> \<lparr>node_mark = RuleMarkNode_Blue , node_label = [Var ''a''], node_rooted = False\<rparr>
                                ,1 \<mapsto> \<lparr>node_mark = RuleMarkNode_Red, node_label = [Var ''b''], node_rooted = False\<rparr>]
                       ,edges = [1 \<mapsto> \<lparr>edge_src = 1, edge_trg = 2, edge_mark = RuleMarkEdge_None, edge_label = [Var ''c'']\<rparr>]\<rparr>
           ,rule_interf = {1,2}\<rparr>"

definition ill_blue :: ruleschema where
"ill_blue = \<lparr>rule_ty = [''a'' \<mapsto> Lty, ''b'' \<mapsto> Lty, ''c'' \<mapsto> Lty]
            ,rule_lhs = \<lparr>nodes = [1 \<mapsto> \<lparr>node_mark = RuleMarkNode_Blue, node_label = [Var ''a''], node_rooted = False\<rparr>
                                 ,1 \<mapsto> \<lparr>node_mark = RuleMarkNode_Blue, node_label = [Var ''b''], node_rooted = False\<rparr>]
                        ,edges = [1 \<mapsto> \<lparr>edge_src = 1, edge_trg = 2, edge_mark = RuleMarkEdge_None, edge_label = [Var ''c'']\<rparr>]\<rparr>
            ,rule_rhs = \<lparr>nodes = [1 \<mapsto> \<lparr>node_mark = RuleMarkNode_Blue, node_label = [Var ''a''], node_rooted = False\<rparr>
                                 ,1 \<mapsto> \<lparr>node_mark = RuleMarkNode_Blue, node_label = [Var ''b''], node_rooted = False\<rparr>]
                        ,edges = [1 \<mapsto> \<lparr>edge_src = 1, edge_trg = 2, edge_mark = RuleMarkEdge_None, edge_label = [Var ''c'']\<rparr>]\<rparr>
            ,rule_interf = {1,2}\<rparr>"

definition ill_red :: ruleschema where
"ill_red = \<lparr>rule_ty = [''a'' \<mapsto> Lty, ''b'' \<mapsto> Lty, ''c'' \<mapsto> Lty]
           ,rule_lhs = \<lparr>nodes = [1 \<mapsto> \<lparr>node_mark = RuleMarkNode_Red, node_label = [Var ''a''], node_rooted = False\<rparr>
                                ,1 \<mapsto> \<lparr>node_mark = RuleMarkNode_Red, node_label = [Var ''b''], node_rooted = False\<rparr>]
                       ,edges = [1 \<mapsto> \<lparr>edge_src = 1, edge_trg = 2, edge_mark = RuleMarkEdge_None, edge_label = [Var ''c'']\<rparr>]\<rparr>
           ,rule_rhs = \<lparr>nodes = [1 \<mapsto> \<lparr>node_mark = RuleMarkNode_Red, node_label = [Var ''a''], node_rooted = False\<rparr>
                                ,1 \<mapsto> \<lparr>node_mark = RuleMarkNode_Red, node_label = [Var ''b''], node_rooted = False\<rparr>]
                       ,edges = [1 \<mapsto> \<lparr>edge_src = 1, edge_trg = 2, edge_mark = RuleMarkEdge_None, edge_label = [Var ''c'']\<rparr>]\<rparr>
           ,rule_interf = {1,2}\<rparr>"


definition twocolouring :: com where
"twocolouring \<equiv> (RuleApp init ;; RuleSet {col_blue :: rule, col_red:: rule}!)! ;; 
  IF RuleSet {ill_blue :: rule, ill_red :: rule} THEN RuleApp unmark! ELSE Skip"


abbreviation c :: "form" where
"c == (\<lceil>\<forall> ''x'' : Node\<rceil> \<lceil>mark \<langle>''x''\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_None \<lceil>\<and>\<rceil> \<lceil>unrooted \<langle>''x''\<rangle>\<rceil>) \<lceil>\<and>\<rceil>
      (\<lceil>\<forall> ''x'' : Edge\<rceil> \<lceil>mark \<langle>''x''\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>E RuleMarkEdge_None)"


abbreviation d :: form where
"d == (\<lceil>\<forall> ''x'' : Node\<rceil> \<lceil>mark \<langle>''x''\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Red  \<lceil>\<or>\<rceil>\<lceil>mark \<langle>''x''\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Blue) \<lceil>\<and>\<rceil>
      \<lceil>\<not>\<rceil>(\<lceil>\<exists> ''x'' : Edge\<rceil> (\<lceil>src \<langle>''x''\<rangle>\<rceil> \<lceil>\<noteq>\<rceil> \<lceil>trg \<langle>''x''\<rangle>\<rceil>) \<lceil>\<and>\<rceil>
                     \<lceil>mark \<lceil>src \<langle>''x''\<rangle>\<rceil>\<rceil> \<lceil>=\<rceil> \<lceil>mark \<lceil>trg \<langle>''x''\<rangle>\<rceil>\<rceil>)"

abbreviation e :: form where
"e == (\<lceil>\<forall> ''x'' : Node\<rceil> (\<lceil>mark \<langle>''x''\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Red \<lceil>\<or>\<rceil> \<lceil>mark \<langle>''x''\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Blue) \<lceil>\<and>\<rceil> \<lceil>unrooted \<langle>''x''\<rangle>\<rceil>) \<lceil>\<and>\<rceil>
      (\<lceil>\<forall> ''x'' : Edge\<rceil>  \<lceil>mark \<langle>''x''\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>E RuleMarkEdge_None)"

abbreviation f :: form where
"f == (\<lceil>\<forall> ''x'' : Node\<rceil> (\<lceil>mark \<langle>''x''\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Red \<lceil>\<or>\<rceil> \<lceil>mark \<langle>''x''\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_Blue \<lceil>\<or>\<rceil> 
        \<lceil>mark \<langle>''x''\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>V RuleMarkNode_None) \<lceil>\<and>\<rceil> \<lceil>unrooted \<langle>''x''\<rangle>\<rceil>) \<lceil>\<and>\<rceil>
      (\<lceil>\<forall> ''x'' : Edge\<rceil>  \<lceil>mark \<langle>''x''\<rangle>\<rceil> \<lceil>=\<rceil> \<triangleright>\<^sub>E RuleMarkEdge_None)"


lemma c_impl_f : "eval g undefined (c \<lceil>\<longrightarrow>\<rceil> f)" 
  by clarsimp

 

lemma "\<turnstile> {c} twocolouring {c \<lceil>\<or>\<rceil> d}"
  apply (simp add: twocolouring_def)
  apply (rule Cons [where ?c' = f and ?d' = "c \<lceil>\<or>\<rceil> d"])
    apply auto
  apply (rule Comp [where ?e = e])
\<comment> \<open>subtree I\<close>
   apply (rule Cons [where ?c' = f and d'="f \<lceil>\<and>\<rceil> Fail (RuleApp init ;; RuleSet {col_blue::rule, col_red::rule}!)"])
  apply auto


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