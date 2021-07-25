theory Common
  imports Main "HOL-Library.Mapping"
begin

fun mfold :: "('k :: linorder, 'v) mapping \<Rightarrow> ('k \<times> 'v \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> 'c" where
"mfold m r i = 
  (let f = \<lambda>k a. r (k, the (Mapping.lookup m k)) a in foldr f (Mapping.ordered_keys m) i)"
(* 
fun mfold :: "('a :: linorder \<rightharpoonup> 'b) \<Rightarrow> ('a \<times> 'b \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> 'c" where
"mfold m f i = (let v = sorted_list_of_set (dom m);
                    z = zip v (map (the \<circ> m) v)
                in fold f z i)"
 *)
(* https://stackoverflow.com/questions/28633353/converting-a-set-to-a-list-in-isabelle *)
definition set_to_list :: "'a set \<Rightarrow> 'a list"
  where "set_to_list s = (SOME l. set l = s)"

lemma  set_set_to_list:
   "finite s \<Longrightarrow> set (set_to_list s) = s"
  unfolding set_to_list_def by (metis (mono_tags) finite_list some_eq_ex)

end