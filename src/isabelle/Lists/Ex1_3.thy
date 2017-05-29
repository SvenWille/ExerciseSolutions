theory Ex1_3 
imports Main
begin 


fun alls :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where   
"alls _ [] = True"|
"alls cond (x#xs) =  (cond x \<and> alls cond xs)"


fun exs :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where 
"exs cond [] = False"|
"exs cond (x#xs) = (if cond x then True else exs cond xs)"



lemma "alls (\<lambda>x . P x \<and> Q x) xs = (alls P xs \<and> alls Q xs)" 
proof (induct xs)
  show "alls (\<lambda>x. P x \<and> Q x) [] = (alls P [] \<and> alls Q [])" by simp
 next 
  fix a xs 
  assume "alls (\<lambda>x. P x \<and> Q x) xs = (alls P xs \<and> alls Q xs)"
  thus "alls (\<lambda>x. P x \<and> Q x) (a # xs) = (alls P (a # xs) \<and> alls Q (a # xs))" by auto
qed

lemma tmp [simp] : "alls P (xs @ [x]) = (alls P xs \<and> P x)" 
proof (induct xs)
  case Nil 
  show ?case by simp
 next 
  fix a xs 
  case (Cons a xs)
  assume " alls P (xs @ [x]) = (alls P xs \<and> P x)"
  thus ?case by simp
qed

lemma "alls P (rev xs) = alls P xs "
proof (induct xs) 
  case Nil 
  show ?case by simp
 next 
  fix a xs
  case (Cons a xs)

  assume " alls P (rev xs) = alls P xs"
  thus ?case by auto
qed

(*
lemma "exs (\<lambda>x . P x \<and> Q x) xs = (exs P xs \<and> exs Q xs)"
proof (induct xs)
  case Nil 
  show ?case by simp
 next 
  fix a xs 
  case (Cons a xs)
  assume "exs (\<lambda>x. P x \<and> Q x) xs = (exs P xs \<and> exs Q xs)"
  show " exs (\<lambda>x. P x \<and> Q x) (a # xs) = (exs P (a # xs) \<and> exs Q (a # xs))" 
*)